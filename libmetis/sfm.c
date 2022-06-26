/*
 * Copyright 1997, Regents of the University of Minnesota
 *
 * sfm.c
 *
 * This file contains code that implementes an FM-based separator refinement
 *
 * Started 8/1/97
 * George
 *
 * $Id: sfm.c 10874 2011-10-17 23:13:00Z karypis $
 *
 */

#include "metislib.h"

#if DEBUG_TWO_SIDED
#define debug_two(...) fprintf(stderr, __VA_ARGS__)
#else
#define debug_two(...)
#endif

#if DEBUG_ONE_SIDED
#define debug_one(...) fprintf(stderr, __VA_ARGS__)
#else
#define debug_one(...)
#endif

#if DEBUG_BALANCE
#define debug_bal(...) fprintf(stderr, __VA_ARGS__)
#else
#define debug_bal(...)
#endif

/*************************************************************************/
/*! This function performs a node-based FM refinement */
/**************************************************************************/
void FM_2WayNodeRefine2Sided(ctrl_t *ctrl, graph_t *graph, idx_t niter)
{
  idx_t i, ii, j, k, jj, kk, nvtxs, nbnd, nswaps, nmind;
  idx_t *xadj, *vwgt, *adjncy, *where, *pwgts, *edegrees, *bndind, *bndptr;
  idx_t *mptr, *mind, *moved, *swaps;
  rpq_t *queues[2]; 
  nrinfo_t *rinfo;
  idx_t higain, oldgain, mincut, initcut, mincutorder;	
  idx_t pass, to, other, limit;
  idx_t badmaxpwgt, mindiff, newdiff;
  idx_t u[2], g[2];
  real_t mult;   

  debug_two("ENTERING TWO_WAY_NODE_REFINE_TWO_SIDED\n");
#if DEBUG_TWO_SIDED
  PrintGraph(graph);
  PrintWhereIdEd(graph);
  PrintBoundaryInfo(graph);
#endif
  debug_two("nrinfo: [");
  for (int i = 0; i < graph->nvtxs; i++) {
    debug_two("(%ld, %ld), ", graph->nrinfo[i].edegrees[0], graph->nrinfo[i].edegrees[1]);
  }
  debug_two("]\n");

  WCOREPUSH;

  nvtxs  = graph->nvtxs;
  xadj   = graph->xadj;
  adjncy = graph->adjncy;
  vwgt   = graph->vwgt;

  bndind = graph->bndind;
  bndptr = graph->bndptr;
  where  = graph->where;
  pwgts  = graph->pwgts;
  rinfo  = graph->nrinfo;

  queues[0] = rpqCreate(nvtxs);
  queues[1] = rpqCreate(nvtxs);

  moved = iwspacemalloc(ctrl, nvtxs);
  swaps = iwspacemalloc(ctrl, nvtxs);
  mptr  = iwspacemalloc(ctrl, nvtxs+1);
  mind  = iwspacemalloc(ctrl, 2*nvtxs);

  mult = 0.5*ctrl->ubfactors[0];
  badmaxpwgt = (idx_t)(mult*(pwgts[0]+pwgts[1]+pwgts[2]));

  IFSET(ctrl->dbglvl, METIS_DBG_REFINE,
    printf("Partitions-N2: [%6"PRIDX" %6"PRIDX"] Nv-Nb[%6"PRIDX" %6"PRIDX"]. ISep: %6"PRIDX"\n", pwgts[0], pwgts[1], graph->nvtxs, graph->nbnd, graph->mincut));

  for (pass=0; pass<niter; pass++) {
    iset(nvtxs, -1, moved);
    rpqReset(queues[0]);
    rpqReset(queues[1]);

    mincutorder = -1;
    initcut = mincut = graph->mincut;
    nbnd = graph->nbnd;

    /* use the swaps array in place of the traditional perm array to save memory */
    irandArrayPermute(nbnd, swaps, nbnd, 1);
    for (ii=0; ii<nbnd; ii++) {
      i = bndind[swaps[ii]];
      ASSERT(where[i] == 2);
      rpqInsert(queues[0], i, vwgt[i]-rinfo[i].edegrees[1]);
      rpqInsert(queues[1], i, vwgt[i]-rinfo[i].edegrees[0]);
    }

    ASSERT(CheckNodeBnd(graph, nbnd));
    ASSERT(CheckNodePartitionParams(graph));

    limit = (ctrl->compress ? gk_min(5*nbnd, 400) : gk_min(2*nbnd, 300));

    /******************************************************
    * Get into the FM loop
    *******************************************************/
    mptr[0] = nmind = 0;
    mindiff = iabs(pwgts[0]-pwgts[1]);
    to = (pwgts[0] < pwgts[1] ? 0 : 1);
    for (nswaps=0; nswaps<nvtxs; nswaps++) {
      for (int i = 0; i < 5; i++) {
        debug_two("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
      }
      debug_two("N_SWAPS: %ld\n", nswaps);
      debug_two("where: [");
      for (int i = 0; i < graph->nvtxs; i++) {
        debug_two("%ld, ", graph->where[i]);
      }
      debug_two("]\n");
      #if DEBUG_TWO_SIDED
      PrintBoundaryInfo(graph);
      #endif
      debug_two("swaps: [");
      for (int i = 0; i < nvtxs; i++) {
        debug_two("%ld, ", swaps[i]);
      }
      debug_two("]\n");
      debug_two("moved: [");
      for (int i = 0; i < graph->nvtxs; i++) {
        debug_two("%ld, ", moved[i]);
      }
      debug_two("]\n");
      for (int qi = 0; qi < 2; qi++) {
        debug_two("queue %d: {\n", qi);
        debug_two("nnodes: %ld\n", queues[qi]->nnodes);
        debug_two("heap: [");
        for (int i = 0; i < queues[qi]->maxnodes; i++) {
          rkv_t* node = &queues[qi]->heap[i];
          debug_two("(%f, %ld), ", node->key, node->val);
        }
        debug_two("]\n");
        debug_two("locator: [");
        for (int i = 0; i < queues[qi]->maxnodes; i++) {
          debug_two("%ld, ", queues[qi]->locator[i]);
        }
        debug_two("]\n");
      }
      debug_two("mincutorder: %ld\n", mincutorder);
      debug_two("mincut: %ld\n", mincut);
      debug_two("m_ptr: [");
      for (int i = 0; i < graph->nvtxs + 1; i++) {
        debug_two("%ld, ", mptr[i]);
      }
      debug_two("]\n");
      debug_two("min_diff: %ld\n", mindiff);


      u[0] = rpqSeeTopVal(queues[0]);  
      u[1] = rpqSeeTopVal(queues[1]);
      if (u[0] != -1 && u[1] != -1) {
        g[0] = vwgt[u[0]]-rinfo[u[0]].edegrees[1];
        g[1] = vwgt[u[1]]-rinfo[u[1]].edegrees[0];

        to = (g[0] > g[1] ? 0 : (g[0] < g[1] ? 1 : pass%2)); 

        if (pwgts[to]+vwgt[u[to]] > badmaxpwgt) 
          to = (to+1)%2;
      }
      else if (u[0] == -1 && u[1] == -1) {
        break;
      }
      else if (u[0] != -1 && pwgts[0]+vwgt[u[0]] <= badmaxpwgt) {
        to = 0;
      }
      else if (u[1] != -1 && pwgts[1]+vwgt[u[1]] <= badmaxpwgt) {
        to = 1;
      }
      else
        break;

      other = (to+1)%2;

      higain = rpqGetTop(queues[to]);

      if (moved[higain] == -1) /* Delete if it was in the separator originally */
        rpqDelete(queues[other], higain);

      ASSERT(bndptr[higain] != -1);

      /* The following check is to ensure we break out if there is a posibility
         of over-running the mind array.  */
      if (nmind + xadj[higain+1]-xadj[higain] >= 2*nvtxs-1) 
        break;

      pwgts[2] -= (vwgt[higain]-rinfo[higain].edegrees[other]);

      newdiff = iabs(pwgts[to]+vwgt[higain] - (pwgts[other]-rinfo[higain].edegrees[other]));
      if (pwgts[2] < mincut || (pwgts[2] == mincut && newdiff < mindiff)) {
        mincut = pwgts[2];
        mincutorder = nswaps;
        mindiff = newdiff;
      }
      else {
        if (nswaps - mincutorder > 2*limit || 
            (nswaps - mincutorder > limit && pwgts[2] > 1.10*mincut)) {
          pwgts[2] += (vwgt[higain]-rinfo[higain].edegrees[other]);
          break; /* No further improvement, break out */
        }
      }

      BNDDelete(nbnd, bndind, bndptr, higain);
      pwgts[to] += vwgt[higain];
      where[higain] = to;
      moved[higain] = nswaps;
      swaps[nswaps] = higain;  


      /**********************************************************
      * Update the degrees of the affected nodes
      ***********************************************************/
      for (j=xadj[higain]; j<xadj[higain+1]; j++) {
        k = adjncy[j];
        if (where[k] == 2) { /* For the in-separator vertices modify their edegree[to] */
          oldgain = vwgt[k]-rinfo[k].edegrees[to];
          debug_two("-------- Branch 1, Moved %ld, other %ld, k %ld, new %ld\n", moved[k], other, k, oldgain-vwgt[higain]);
          rinfo[k].edegrees[to] += vwgt[higain];
          if (moved[k] == -1 || moved[k] == -(2+other))
            rpqUpdate(queues[other], k, oldgain-vwgt[higain]);
        }
        else if (where[k] == other) { /* This vertex is pulled into the separator */
          ASSERTP(bndptr[k] == -1, ("%"PRIDX" %"PRIDX" %"PRIDX"\n", k, bndptr[k], where[k]));
          BNDInsert(nbnd, bndind, bndptr, k);

          mind[nmind++] = k;  /* Keep track for rollback */
          where[k] = 2;
          pwgts[other] -= vwgt[k];

          debug_two("--------- Branch 2\n");
          debug_two("where: [");
          for (int i = 0; i < graph->nvtxs; i++) {
            debug_two("%ld, ", graph->where[i]);
          }
          debug_two("]\n");

          edegrees = rinfo[k].edegrees;
          edegrees[0] = edegrees[1] = 0;
          for (jj=xadj[k]; jj<xadj[k+1]; jj++) {
            kk = adjncy[jj];
            if (where[kk] != 2) 
              edegrees[where[kk]] += vwgt[kk];
            else {
              oldgain = vwgt[kk]-rinfo[kk].edegrees[other];
              rinfo[kk].edegrees[other] -= vwgt[k];
              debug_two("Moved %ld, to %ld, k %ld, kk %ld, new %ld\n", moved[kk], to, k, kk, oldgain+vwgt[higain]);
              if (moved[kk] == -1 || moved[kk] == -(2+to))
                rpqUpdate(queues[to], kk, oldgain+vwgt[k]);
            }
          }
          debug_two("Set nrinfo %ld to (%ld, %ld)\n", k, edegrees[0], edegrees[1]);

          /* Insert the new vertex into the priority queue. Only one side! */
          if (moved[k] == -1) {
            rpqInsert(queues[to], k, vwgt[k]-edegrees[other]);
            moved[k] = -(2+to);
          }
        }
      }
      mptr[nswaps+1] = nmind;

      IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
            printf("Moved %6"PRIDX" to %3"PRIDX", Gain: %5"PRIDX" [%5"PRIDX"] [%4"PRIDX" %4"PRIDX"] \t[%5"PRIDX" %5"PRIDX" %5"PRIDX"]\n", higain, to, g[to], g[other], vwgt[u[to]], vwgt[u[other]], pwgts[0], pwgts[1], pwgts[2]));

    }


    /****************************************************************
    * Roll back computation 
    *****************************************************************/
    for (nswaps--; nswaps>mincutorder; nswaps--) {
      higain = swaps[nswaps];
      debug_two("Rolling %ld, [", higain);
      for (int i = mptr[nswaps]; i < mptr[nswaps + 1]; i++) {
        debug_two("%ld, ", mind[i]);
      }
      debug_two("]\n");
      #if DEBUG_TWO_SIDED
      PrintWhereIdEd(graph);
      #endif

      ASSERT(CheckNodePartitionParams(graph));

      to = where[higain];
      other = (to+1)%2;
      INC_DEC(pwgts[2], pwgts[to], vwgt[higain]);
      where[higain] = 2;
      BNDInsert(nbnd, bndind, bndptr, higain);

      edegrees = rinfo[higain].edegrees;
      edegrees[0] = edegrees[1] = 0;
      for (j=xadj[higain]; j<xadj[higain+1]; j++) {
        k = adjncy[j];
        if (where[k] == 2) 
          rinfo[k].edegrees[to] -= vwgt[higain];
        else
          edegrees[where[k]] += vwgt[k];
      }

      /* Push nodes out of the separator */
      for (j=mptr[nswaps]; j<mptr[nswaps+1]; j++) {
        k = mind[j];
        ASSERT(where[k] == 2);
        where[k] = other;
        INC_DEC(pwgts[other], pwgts[2], vwgt[k]);
        BNDDelete(nbnd, bndind, bndptr, k);
        for (jj=xadj[k]; jj<xadj[k+1]; jj++) {
          kk = adjncy[jj];
          if (where[kk] == 2) 
            rinfo[kk].edegrees[other] += vwgt[k];
        }
      }
    }

    ASSERT(mincut == pwgts[2]);

    IFSET(ctrl->dbglvl, METIS_DBG_REFINE,
      printf("\tMinimum sep: %6"PRIDX" at %5"PRIDX", PWGTS: [%6"PRIDX" %6"PRIDX"], NBND: %6"PRIDX"\n", mincut, mincutorder, pwgts[0], pwgts[1], nbnd));

    graph->mincut = mincut;
    graph->nbnd = nbnd;

    if (mincutorder == -1 || mincut >= initcut)
      break;
  }

  rpqDestroy(queues[0]);
  rpqDestroy(queues[1]);

  WCOREPOP;
}


/*************************************************************************/
/*! This function performs a node-based FM refinement. 
    Each refinement iteration is split into two sub-iterations. 
    In each sub-iteration only moves to one of the left/right partitions 
    is allowed; hence, it is one-sided. 
*/
/**************************************************************************/
void FM_2WayNodeRefine1Sided(ctrl_t *ctrl, graph_t *graph, idx_t niter)
{
  idx_t i, ii, j, k, jj, kk, nvtxs, nbnd, nswaps, nmind, iend;
  idx_t *xadj, *vwgt, *adjncy, *where, *pwgts, *edegrees, *bndind, *bndptr;
  idx_t *mptr, *mind, *swaps;
  rpq_t *queue; 
  nrinfo_t *rinfo;
  idx_t higain, mincut, initcut, mincutorder;	
  idx_t pass, to, other, limit;
  idx_t badmaxpwgt, mindiff, newdiff;
  real_t mult;

  debug_one("CALLED two_way_node_refine_one_sided\n");

  #if DEBUG_ONE_SIDED
  PrintGraph(graph);
  debug_one("\n");
  PrintWhereIdEd(graph);
  PrintBoundaryInfo(graph);
  #endif
  // debug_one("nrinfo: [");
  // for (int i = 0; i < graph->nvtxs; i++) {
  //   debug_one("(%ld, %ld), ", graph->nrinfo[i].edegrees[0], graph->nrinfo[i].edegrees[1]);
  // }
  // debug_one("]\n");
  debug_one("n_iterations: %ld\n", niter);
  WCOREPUSH;

  nvtxs  = graph->nvtxs;
  xadj   = graph->xadj;
  adjncy = graph->adjncy;
  vwgt   = graph->vwgt;

  bndind = graph->bndind;
  bndptr = graph->bndptr;
  where  = graph->where;
  pwgts  = graph->pwgts;
  rinfo  = graph->nrinfo;

  queue = rpqCreate(nvtxs);

  swaps = iwspacemalloc(ctrl, nvtxs);
  mptr  = iwspacemalloc(ctrl, nvtxs+1);
  mind  = iwspacemalloc(ctrl, 2*nvtxs);

  mult = 0.5*ctrl->ubfactors[0];
  badmaxpwgt = (idx_t)(mult*(pwgts[0]+pwgts[1]+pwgts[2]));

  IFSET(ctrl->dbglvl, METIS_DBG_REFINE,
    printf("Partitions-N1: [%6"PRIDX" %6"PRIDX"] Nv-Nb[%6"PRIDX" %6"PRIDX"]. ISep: %6"PRIDX"\n", pwgts[0], pwgts[1], graph->nvtxs, graph->nbnd, graph->mincut));

  to = (pwgts[0] < pwgts[1] ? 1 : 0);
  for (pass=0; pass<2*niter; pass++) {  /* the 2*niter is for the two sides */
    other = to; 
    to    = (to+1)%2;
    debug_one("NEW PASS %ld (%ld, %ld)\n", pass, to, other);

    #if DEBUG_ONE_SIDED
    debug_one("pre reset: ");
    PrintPriorityQueue(queue);
    debug_one("\n");
    #endif

    rpqReset(queue);

    #if DEBUG_ONE_SIDED
    debug_one("after reset: ");
    PrintPriorityQueue(queue);
    debug_one("\n");
    #endif

    mincutorder = -1;
    initcut = mincut = graph->mincut;
    nbnd = graph->nbnd;

    /* use the swaps array in place of the traditional perm array to save memory */
    irandArrayPermute(nbnd, swaps, nbnd, 1);
    _PRINT_LIST_NAME(perm, swaps, nbnd, DEBUG_ONE_SIDED);
    debug_one("\n");
    for (ii=0; ii<nbnd; ii++) {
      i = bndind[swaps[ii]];
      ASSERT(where[i] == 2);

      #if DEBUG_ONE_SIDED
      debug_one("pre insert: ");
      PrintPriorityQueue(queue);
      debug_one("\n");
      #endif

      debug_one("i: %ld, vwgt: %ld, other: %ld, deg: %ld\n", i, vwgt[i], other, rinfo[i].edegrees[other]);
      rpqInsert(queue, i, vwgt[i]-rinfo[i].edegrees[other]);

      #if DEBUG_ONE_SIDED
      debug_one("post insert: ");
      PrintPriorityQueue(queue);
      debug_one("\n");
      #endif
    }

    ASSERT(CheckNodeBnd(graph, nbnd));
    ASSERT(CheckNodePartitionParams(graph));

    limit = (ctrl->compress ? gk_min(5*nbnd, 500) : gk_min(3*nbnd, 300));

    /******************************************************
    * Get into the FM loop
    *******************************************************/
    IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->Aux3Tmr));
    mptr[0] = nmind = 0;
    mindiff = iabs(pwgts[0]-pwgts[1]);
    for (nswaps=0; nswaps<nvtxs; nswaps++) {
      debug_one("SWAP %ld\n", nswaps);
      #if DEBUG_ONE_SIDED
      PrintWhereIdEd(graph);
      PrintBoundaryInfoEek(graph, nbnd);
      PrintPriorityQueue(queue);
      debug_one("\n");
      #endif
      debug_one("to: %ld, other: %ld\n", to, other);
      _PRINT_LIST(swaps, nswaps, DEBUG_ONE_SIDED)
      debug_one("\n");
      if (mincutorder == -1) {
        debug_one("min_cut_order: None\n");
      } else {
        debug_one("min_cut_order: Some(%ld)\n", mincutorder);
      }
      debug_one("min_cut: %ld\n", mincut);
      debug_one("m_ptr: [");
      for (int i = 0; i < nswaps; i++) {
        debug_one("[");
        for (int j = mptr[i]; j < mptr[i + 1]; j++) {
          debug_one("%ld", mind[j]);
          if (j + 1 != mptr[i + 1]) {
            debug_one(", ");
          }
        }
        debug_one("]");
        if (i + 1 != nswaps) {
          debug_one(", ");
        }
      }
      debug_one("]\n");
      debug_one("min_diff: %ld\n", mindiff);

      if ((higain = rpqGetTop(queue)) == -1)
        break;

      ASSERT(bndptr[higain] != -1);

      /* The following check is to ensure we break out if there is a posibility
         of over-running the mind array.  */
      if (nmind + xadj[higain+1]-xadj[higain] >= 2*nvtxs-1)
        break;

      debug_one("pwgt: %ld, vwgt: %ld, bmpw: %ld\n", pwgts[to], vwgt[higain], badmaxpwgt);
      if (pwgts[to]+vwgt[higain] > badmaxpwgt)  {
        debug_one("Break 469\n");
        break;  /* No point going any further. Balance will be bad */
      }

      pwgts[2] -= (vwgt[higain]-rinfo[higain].edegrees[other]);

      newdiff = iabs(pwgts[to]+vwgt[higain] - (pwgts[other]-rinfo[higain].edegrees[other]));
      if (pwgts[2] < mincut || (pwgts[2] == mincut && newdiff < mindiff)) {
        mincut      = pwgts[2];
        mincutorder = nswaps;
        mindiff     = newdiff;
      }
      else {
        if (nswaps - mincutorder > 3*limit || 
            (nswaps - mincutorder > limit && pwgts[2] > 1.10*mincut)) {
          pwgts[2] += (vwgt[higain]-rinfo[higain].edegrees[other]);
          break; /* No further improvement, break out */
        }
      }

      debug_one("high_gain: %ld\n", higain);
      BNDDelete(nbnd, bndind, bndptr, higain);
      pwgts[to]     += vwgt[higain];
      where[higain]  = to;
      swaps[nswaps]  = higain;  


      /**********************************************************
      * Update the degrees of the affected nodes
      ***********************************************************/
      IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->Aux1Tmr));
      for (j=xadj[higain]; j<xadj[higain+1]; j++) {
        k = adjncy[j];
        debug_one("Neighbor %ld\n", k);

        if (where[k] == 2) { /* For the in-separator vertices modify their edegree[to] */
          debug_one("Branch 1\n");
          rinfo[k].edegrees[to] += vwgt[higain];
        }
        else if (where[k] == other) { /* This vertex is pulled into the separator */
          debug_one("Branch 2\n");
          ASSERTP(bndptr[k] == -1, ("%"PRIDX" %"PRIDX" %"PRIDX"\n", k, bndptr[k], where[k]));
          debug_one("Inserting k %ld\n", k);
          BNDInsert(nbnd, bndind, bndptr, k);

          mind[nmind++] = k;  /* Keep track for rollback */
          where[k] = 2;
          pwgts[other] -= vwgt[k];

          edegrees = rinfo[k].edegrees;
          edegrees[0] = edegrees[1] = 0;
          for (jj=xadj[k], iend=xadj[k+1]; jj<iend; jj++) {
            kk = adjncy[jj];
            if (where[kk] != 2) {
              edegrees[where[kk]] += vwgt[kk];
            } else {
              rinfo[kk].edegrees[other] -= vwgt[k];

              /* Since the moves are one-sided this vertex has not been moved yet */
              #if DEBUG_ONE_SIDED
              debug_one("pre update: ");
              PrintPriorityQueue(queue);
              debug_one("\n");
              #endif

              rpqUpdate(queue, kk, vwgt[kk]-rinfo[kk].edegrees[other]); 

              #if DEBUG_ONE_SIDED
              debug_one("post update: ");
              PrintPriorityQueue(queue);
              debug_one("\n");
              #endif
            }
          }

          /* Insert the new vertex into the priority queue. Safe due to one-sided moves */
          #if DEBUG_ONE_SIDED
          debug_one("pre insert 2: ");
          PrintPriorityQueue(queue);
          debug_one("\n");
          #endif

          rpqInsert(queue, k, vwgt[k]-edegrees[other]);

          #if DEBUG_ONE_SIDED
          debug_one("post insert 2: ");
          PrintPriorityQueue(queue);
          debug_one("\n");
          #endif
        }
      }
      mptr[nswaps+1] = nmind;
      IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->Aux1Tmr));


      IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
            printf("Moved %6"PRIDX" to %3"PRIDX", Gain: %5"PRIDX" [%5"PRIDX"] \t[%5"PRIDX" %5"PRIDX" %5"PRIDX"] [%3"PRIDX" %2"PRIDX"]\n", 
                higain, to, (vwgt[higain]-rinfo[higain].edegrees[other]), vwgt[higain], 
                pwgts[0], pwgts[1], pwgts[2], nswaps, limit));
    }
    IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->Aux3Tmr));


    /****************************************************************
    * Roll back computation 
    *****************************************************************/
    IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->Aux2Tmr));
    for (nswaps--; nswaps>mincutorder; nswaps--) {
      higain = swaps[nswaps];

      ASSERT(CheckNodePartitionParams(graph));
      ASSERT(where[higain] == to);

      INC_DEC(pwgts[2], pwgts[to], vwgt[higain]);
      where[higain] = 2;
      BNDInsert(nbnd, bndind, bndptr, higain);

      edegrees = rinfo[higain].edegrees;
      edegrees[0] = edegrees[1] = 0;
      for (j=xadj[higain]; j<xadj[higain+1]; j++) {
        k = adjncy[j];
        if (where[k] == 2) 
          rinfo[k].edegrees[to] -= vwgt[higain];
        else
          edegrees[where[k]] += vwgt[k];
      }

      /* Push nodes out of the separator */
      for (j=mptr[nswaps]; j<mptr[nswaps+1]; j++) {
        k = mind[j];
        ASSERT(where[k] == 2);
        where[k] = other;
        INC_DEC(pwgts[other], pwgts[2], vwgt[k]);
        BNDDelete(nbnd, bndind, bndptr, k);
        for (jj=xadj[k], iend=xadj[k+1]; jj<iend; jj++) {
          kk = adjncy[jj];
          if (where[kk] == 2) 
            rinfo[kk].edegrees[other] += vwgt[k];
        }
      }
    }
    IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->Aux2Tmr));

    ASSERT(mincut == pwgts[2]);

    IFSET(ctrl->dbglvl, METIS_DBG_REFINE,
      printf("\tMinimum sep: %6"PRIDX" at %5"PRIDX", PWGTS: [%6"PRIDX" %6"PRIDX"], NBND: %6"PRIDX"\n", mincut, mincutorder, pwgts[0], pwgts[1], nbnd));

    graph->mincut = mincut;
    graph->nbnd   = nbnd;

    if (pass%2 == 1 && (mincutorder == -1 || mincut >= initcut))
      break;
  }

  rpqDestroy(queue);

  debug_one("EXITED two_way_node_refine_one_sided\n");

  WCOREPOP;
}


/*************************************************************************/
/*! This function balances the left/right partitions of a separator 
    tri-section */
/*************************************************************************/
void FM_2WayNodeBalance(ctrl_t *ctrl, graph_t *graph)
{
  idx_t i, ii, j, k, jj, kk, nvtxs, nbnd, nswaps, gain;
  idx_t badmaxpwgt, higain, oldgain, pass, to, other;
  idx_t *xadj, *vwgt, *adjncy, *where, *pwgts, *edegrees, *bndind, *bndptr;
  idx_t *perm, *moved;
  rpq_t *queue; 
  nrinfo_t *rinfo;
  real_t mult;

  debug_bal("CALLED two_way_node_balance\n");
  #if DEBUG_BALANCE
  PrintGraph(graph);
  debug_bal("\n");
  PrintWhereIdEd(graph);
  PrintBoundaryInfo(graph);
  #endif

  nvtxs  = graph->nvtxs;
  xadj   = graph->xadj;
  adjncy = graph->adjncy;
  vwgt   = graph->vwgt;

  bndind = graph->bndind;
  bndptr = graph->bndptr;
  where  = graph->where;
  pwgts  = graph->pwgts;
  rinfo  = graph->nrinfo;

  mult = 0.5*ctrl->ubfactors[0];

  badmaxpwgt = (idx_t)(mult*(pwgts[0]+pwgts[1]));
  if (gk_max(pwgts[0], pwgts[1]) < badmaxpwgt) {
    debug_bal("EARLY EXITED two_way_node_balance\n");
    return;
  }
  if (iabs(pwgts[0]-pwgts[1]) < 3*graph->tvwgt[0]/nvtxs) {
    debug_bal("EARLY EXITED 2 two_way_node_balance\n");
    return;
  }

  WCOREPUSH;

  to    = (pwgts[0] < pwgts[1] ? 0 : 1); 
  other = (to+1)%2;

  queue = rpqCreate(nvtxs);

  perm  = iwspacemalloc(ctrl, nvtxs);
  moved = iset(nvtxs, -1, iwspacemalloc(ctrl, nvtxs));

  IFSET(ctrl->dbglvl, METIS_DBG_REFINE,
    printf("Partitions: [%6"PRIDX" %6"PRIDX"] Nv-Nb[%6"PRIDX" %6"PRIDX"]. ISep: %6"PRIDX" [B]\n", pwgts[0], pwgts[1], graph->nvtxs, graph->nbnd, graph->mincut));

  nbnd = graph->nbnd;
  irandArrayPermute(nbnd, perm, nbnd, 1);
  for (ii=0; ii<nbnd; ii++) {
    i = bndind[perm[ii]];
    ASSERT(where[i] == 2);
    rpqInsert(queue, i, vwgt[i]-rinfo[i].edegrees[other]);
    debug_bal("Inserting %ld %ld\n", i, vwgt[i]-rinfo[i].edegrees[other]);
    #if DEBUG_BALANCE
    PrintPriorityQueue(queue);
    debug_bal("\n");
    #endif
  }

  ASSERT(CheckNodeBnd(graph, nbnd));
  ASSERT(CheckNodePartitionParams(graph));

  /******************************************************
  * Get into the FM loop
  *******************************************************/
  for (nswaps=0; nswaps<nvtxs; nswaps++) {
    debug_bal("SWAP %ld\n", nswaps);
    #if DEBUG_BALANCE
    PrintWhereIdEd(graph);
    PrintBoundaryInfoEek(graph, nbnd);
    PrintPriorityQueue(queue);
    debug_bal("\n");
    #endif
    debug_bal("to: %ld, other: %ld\n", to, other);

    if ((higain = rpqGetTop(queue)) == -1)
      break;

    moved[higain] = 1;

    gain = vwgt[higain]-rinfo[higain].edegrees[other];
    badmaxpwgt = (idx_t)(mult*(pwgts[0]+pwgts[1]));

    /* break if other is now underwight */
    if (pwgts[to] > pwgts[other])
      break;

    /* break if balance is achieved and no +ve or zero gain */
    if (gain < 0 && pwgts[other] < badmaxpwgt) 
      break;

    /* skip this vertex if it will violate balance on the other side */
    if (pwgts[to]+vwgt[higain] > badmaxpwgt) 
      continue;

    ASSERT(bndptr[higain] != -1);

    pwgts[2] -= gain;

    BNDDelete(nbnd, bndind, bndptr, higain);
    pwgts[to] += vwgt[higain];
    where[higain] = to;

    IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
          printf("Moved %6"PRIDX" to %3"PRIDX", Gain: %3"PRIDX", \t[%5"PRIDX" %5"PRIDX" %5"PRIDX"]\n", higain, to, vwgt[higain]-rinfo[higain].edegrees[other], pwgts[0], pwgts[1], pwgts[2]));


    /**********************************************************
    * Update the degrees of the affected nodes
    ***********************************************************/
    for (j=xadj[higain]; j<xadj[higain+1]; j++) {
      k = adjncy[j];
      debug_bal("k: %ld\n", k);
      if (where[k] == 2) { /* For the in-separator vertices modify their edegree[to] */
        rinfo[k].edegrees[to] += vwgt[higain];
      }
      else if (where[k] == other) { /* This vertex is pulled into the separator */
        ASSERTP(bndptr[k] == -1, ("%"PRIDX" %"PRIDX" %"PRIDX"\n", k, bndptr[k], where[k]));
        BNDInsert(nbnd, bndind, bndptr, k);

        where[k] = 2;
        pwgts[other] -= vwgt[k];

        edegrees = rinfo[k].edegrees;
        edegrees[0] = edegrees[1] = 0;
        for (jj=xadj[k]; jj<xadj[k+1]; jj++) {
          kk = adjncy[jj];
          debug_bal("kk: %ld\n", kk);
          if (where[kk] != 2) 
            edegrees[where[kk]] += vwgt[kk];
          else {
            ASSERT(bndptr[kk] != -1);
            oldgain = vwgt[kk]-rinfo[kk].edegrees[other];
            rinfo[kk].edegrees[other] -= vwgt[k];

            if (moved[kk] == -1)
              rpqUpdate(queue, kk, oldgain+vwgt[k]);
          }
        }
        debug_bal("nr_info: %ld\n", nvtxs);

        /* Insert the new vertex into the priority queue */
        rpqInsert(queue, k, vwgt[k]-edegrees[other]);
      }
    }
  }

  IFSET(ctrl->dbglvl, METIS_DBG_REFINE,
    printf("\tBalanced sep: %6"PRIDX" at %4"PRIDX", PWGTS: [%6"PRIDX" %6"PRIDX"], NBND: %6"PRIDX"\n", pwgts[2], nswaps, pwgts[0], pwgts[1], nbnd));

  graph->mincut = pwgts[2];
  graph->nbnd   = nbnd;

  rpqDestroy(queue);

  debug_bal("EXITED two_way_node_balance\n");

  WCOREPOP;
}

