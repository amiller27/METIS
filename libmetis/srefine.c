/*
 * Copyright 1997, Regents of the University of Minnesota
 *
 * srefine.c
 *
 * This file contains code for the separator refinement algortihms
 *
 * Started 8/1/97
 * George
 *
 * $Id: srefine.c 14362 2013-05-21 21:35:23Z karypis $
 *
 */

#include "metislib.h"

#if DEBUG_SEPARATOR_REFINEMENT
#define debug(...) __metis_debug(__VA_ARGS__)
#define DEBUG_SEPARATOR_REFINEMENT_LIST(...) _PRINT_LIST_NAME(__VA_ARGS__)
#else
#define debug(...)
#define DEBUG_SEPARATOR_REFINEMENT_LIST(...)
#endif



/*************************************************************************/
/*! This function is the entry point of the separator refinement. 
    It does not perform any refinement on graph, but it starts by first
    projecting it to the next level finer graph and proceeds from there. */
/*************************************************************************/
void Refine2WayNode(ctrl_t *ctrl, graph_t *orggraph, graph_t *graph)
{

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->UncoarsenTmr));
  
  debug("CALLED refine_two_way_node\n");

  if (graph == orggraph) {
    Compute2WayNodePartitionParams(ctrl, graph);
  }
  else {
    int i = 0;
    do {
      i++;
      graph = graph->finer;

      debug("graph: %d\n", i);
      _PRINT_LIST_NAME(where, graph->coarser->where, graph->coarser->nvtxs, DEBUG_SEPARATOR_REFINEMENT);
      debug("\n");

      graph_ReadFromDisk(ctrl, graph);

      IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->ProjectTmr));
      Project2WayNodePartition(ctrl, graph);
      IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->ProjectTmr));

      IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->RefTmr));
      FM_2WayNodeBalance(ctrl, graph); 

      ASSERT(CheckNodePartitionParams(graph));

      switch (ctrl->rtype) {
        case METIS_RTYPE_SEP2SIDED:
          FM_2WayNodeRefine2Sided(ctrl, graph, ctrl->niter); 
          break;
        case METIS_RTYPE_SEP1SIDED:
          FM_2WayNodeRefine1Sided(ctrl, graph, ctrl->niter); 
          break;
        default:
          gk_errexit(SIGERR, "Unknown rtype of %d\n", ctrl->rtype);
      }
      IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->RefTmr));

    } while (graph != orggraph);
  }

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->UncoarsenTmr));

  debug("EXITED refine_two_way_node\n");
}


/*************************************************************************/
/*! This function allocates memory for 2-way node-based refinement */
/**************************************************************************/
void Allocate2WayNodePartitionMemory(ctrl_t *ctrl, graph_t *graph)
{
  idx_t nvtxs;

  nvtxs = graph->nvtxs;

  graph->pwgts  = imalloc(3, "Allocate2WayNodePartitionMemory: pwgts");
  graph->where  = imalloc(nvtxs, "Allocate2WayNodePartitionMemory: where");
  graph->bndptr = imalloc(nvtxs, "Allocate2WayNodePartitionMemory: bndptr");
  graph->bndind = imalloc(nvtxs, "Allocate2WayNodePartitionMemory: bndind");
  graph->nrinfo = (nrinfo_t *)gk_malloc(nvtxs*sizeof(nrinfo_t), "Allocate2WayNodePartitionMemory: nrinfo");
}


/*************************************************************************/
/*! This function computes the edegrees[] to the left & right sides */
/*************************************************************************/
void Compute2WayNodePartitionParams(ctrl_t *ctrl, graph_t *graph)
{
  idx_t i, j, nvtxs, nbnd;
  idx_t *xadj, *adjncy, *vwgt;
  idx_t *where, *pwgts, *bndind, *bndptr, *edegrees;
  nrinfo_t *rinfo;
  idx_t me, other;

  nvtxs  = graph->nvtxs;
  xadj   = graph->xadj;
  vwgt   = graph->vwgt;
  adjncy = graph->adjncy;

  where  = graph->where;
  rinfo  = graph->nrinfo;
  pwgts  = iset(3, 0, graph->pwgts);
  bndind = graph->bndind;
  bndptr = iset(nvtxs, -1, graph->bndptr);

  debug("CALLED compute_two_way_node_partition_params\n");

  /*------------------------------------------------------------
  / Compute now the separator external degrees
  /------------------------------------------------------------*/
  nbnd = 0;
  for (i=0; i<nvtxs; i++) {
    me = where[i];
    pwgts[me] += vwgt[i];

    ASSERT(me >=0 && me <= 2);

    if (me == 2) { /* If it is on the separator do some computations */
      BNDInsert(nbnd, bndind, bndptr, i);

      edegrees = rinfo[i].edegrees;
      edegrees[0] = edegrees[1] = 0;

      for (j=xadj[i]; j<xadj[i+1]; j++) {
        other = where[adjncy[j]];
        if (other != 2)
          edegrees[other] += vwgt[adjncy[j]];
      }
    }
  }

  ASSERT(CheckNodeBnd(graph, nbnd));

  graph->mincut = pwgts[2];
  graph->nbnd   = nbnd;

  debug("EXITED compute_two_way_node_partition_params\n");
}


/*************************************************************************/
/*! This function projects the node-based bisection */
/*************************************************************************/
void Project2WayNodePartition(ctrl_t *ctrl, graph_t *graph)
{
  idx_t i, j, nvtxs;
  idx_t *cmap, *where, *cwhere;
  graph_t *cgraph;

  debug("CALLED project_two_way_node_partition\n");

  cgraph = graph->coarser;
  cwhere = cgraph->where;

  nvtxs = graph->nvtxs;
  cmap  = graph->cmap;

  debug("graph: ");
  #if DEBUG_SEPARATOR_REFINEMENT
  PrintGraph(graph);
  debug("\n");
  #endif
  DEBUG_SEPARATOR_REFINEMENT_LIST(coarsening_map, graph->cmap, nvtxs, DEBUG_SEPARATOR_REFINEMENT);
  debug("\n");
  DEBUG_SEPARATOR_REFINEMENT_LIST(coarser_graph_where, cgraph->where, cgraph->nvtxs, DEBUG_SEPARATOR_REFINEMENT);
  debug("\n");

  Allocate2WayNodePartitionMemory(ctrl, graph);
  where = graph->where;
  
  /* Project the partition */
  for (i=0; i<nvtxs; i++) {
    where[i] = cwhere[cmap[i]];
    ASSERTP(where[i] >= 0 && where[i] <= 2, ("%"PRIDX" %"PRIDX" %"PRIDX" %"PRIDX"\n", 
          i, cmap[i], where[i], cwhere[cmap[i]]));
  }

  FreeGraph(&graph->coarser);
  graph->coarser = NULL;

  debug("poopy2\n");
  Compute2WayNodePartitionParams(ctrl, graph);

  debug("EXITED project_two_way_node_partition\n");
}
