/*!
\file  
\brief Functions for computing matchings during graph coarsening

\date Started 7/23/97
\author George  
\author Copyright 1997-2011, Regents of the University of Minnesota 
\version\verbatim $Id: coarsen.c 20398 2016-11-22 17:17:12Z karypis $ \endverbatim
*/

#define DEBUG_COARSEN 0

#if DEBUG_COARSEN
#define debug(...) fprintf(stderr, __VA_ARGS__)
#define DEBUG_COARSEN_LIST(...) _PRINT_LIST_NAME(__VA_ARGS)
#else
#define debug(...)
#define DEBUG_COARSEN_LIST(...)
#endif



#include "metislib.h"

#define UNMATCHEDFOR2HOP  0.10  /* The fraction of unmatched vertices that triggers 2-hop */
                                  

/*************************************************************************/
/*! This function takes a graph and creates a sequence of coarser graphs.
    It implements the coarsening phase of the multilevel paradigm. 
 */
/*************************************************************************/
graph_t *CoarsenGraph(ctrl_t *ctrl, graph_t *graph)
{
  idx_t i, eqewgts, level=0;

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->CoarsenTmr));

  /* determine if the weights on the edges are all the same */
  for (eqewgts=1, i=1; i<graph->nedges; i++) {
    if (graph->adjwgt[0] != graph->adjwgt[i]) {
      eqewgts = 0;
      break;
    }
  }

  /* set the maximum allowed coarsest vertex weight */
  for (i=0; i<graph->ncon; i++)
    ctrl->maxvwgt[i] = 1.5*graph->tvwgt[i]/ctrl->CoarsenTo;

  do {
    IFSET(ctrl->dbglvl, METIS_DBG_COARSEN, PrintCGraphStats(ctrl, graph));

    /* allocate memory for cmap, if it has not already been done due to
       multiple cuts */
    if (graph->cmap == NULL)
      graph->cmap = imalloc(graph->nvtxs, "CoarsenGraph: graph->cmap");

    /* determine which matching scheme you will use */
    debug("COMPUTING coarse_graph_result\n");
    #if DEBUG_COARSEN
    PrintGraph(graph);
    debug("\n");
    #endif
    switch (ctrl->ctype) {
      case METIS_CTYPE_RM:
        Match_RM(ctrl, graph);
        break;
      case METIS_CTYPE_SHEM:
        if (eqewgts || graph->nedges == 0) {
          Match_RM(ctrl, graph);
        } else {
          Match_SHEM(ctrl, graph);
        }
        break;
      default:
        gk_errexit(SIGERR, "Unknown ctype: %d\n", ctrl->ctype);
    }

    graph_WriteToDisk(ctrl, graph);

    graph = graph->coarser;
    eqewgts = 0;
    level++;

    ASSERT(CheckGraph(graph, 0, 1));

  } while (graph->nvtxs > ctrl->CoarsenTo && 
           graph->nvtxs < COARSEN_FRACTION*graph->finer->nvtxs && 
           graph->nedges > graph->nvtxs/2);

  IFSET(ctrl->dbglvl, METIS_DBG_COARSEN, PrintCGraphStats(ctrl, graph));
  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->CoarsenTmr));

  debug("EXITING coarsen_graph\n");
  return graph;
}


/*************************************************************************/
/*! This function takes a graph and creates a sequence of nlevels coarser 
    graphs, where nlevels is an input parameter.
 */
/*************************************************************************/
graph_t *CoarsenGraphNlevels(ctrl_t *ctrl, graph_t *graph, idx_t nlevels)
{
  idx_t i, eqewgts, level;

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->CoarsenTmr));

  /* determine if the weights on the edges are all the same */
  for (eqewgts=1, i=1; i<graph->nedges; i++) {
    if (graph->adjwgt[0] != graph->adjwgt[i]) {
      eqewgts = 0;
      break;
    }
  }

  /* set the maximum allowed coarsest vertex weight */
  for (i=0; i<graph->ncon; i++)
    ctrl->maxvwgt[i] = 1.5*graph->tvwgt[i]/ctrl->CoarsenTo;

  for (level=0; level<nlevels; level++) {
    IFSET(ctrl->dbglvl, METIS_DBG_COARSEN, PrintCGraphStats(ctrl, graph));

    /* allocate memory for cmap, if it has not already been done due to
       multiple cuts */
    if (graph->cmap == NULL)
      graph->cmap = imalloc(graph->nvtxs, "CoarsenGraph: graph->cmap");

    /* determine which matching scheme you will use */
    switch (ctrl->ctype) {
      case METIS_CTYPE_RM:
        Match_RM(ctrl, graph);
        break;
      case METIS_CTYPE_SHEM:
        if (eqewgts || graph->nedges == 0)
          Match_RM(ctrl, graph);
        else
          Match_SHEM(ctrl, graph);
        break;
      default:
        gk_errexit(SIGERR, "Unknown ctype: %d\n", ctrl->ctype);
    }

    graph_WriteToDisk(ctrl, graph);

    graph = graph->coarser;
    eqewgts = 0;

    ASSERT(CheckGraph(graph, 0, 1));

    if (graph->nvtxs < ctrl->CoarsenTo || 
        graph->nvtxs > COARSEN_FRACTION*graph->finer->nvtxs || 
        graph->nedges < graph->nvtxs/2)
      break; 
  } 

  IFSET(ctrl->dbglvl, METIS_DBG_COARSEN, PrintCGraphStats(ctrl, graph));
  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->CoarsenTmr));

  return graph;
}


/*************************************************************************/
/*! This function finds a matching by randomly selecting one of the 
    unmatched adjacent vertices. 
 */
/**************************************************************************/
idx_t Match_RM(ctrl_t *ctrl, graph_t *graph)
{
  idx_t i, pi, ii, j, jj, jjinc, k, nvtxs, ncon, cnvtxs, maxidx, 
        last_unmatched, avgdegree, bnum;
  idx_t *xadj, *vwgt, *adjncy, *adjwgt, *maxvwgt;
  idx_t *match, *cmap, *degrees, *perm, *tperm;
  size_t nunmatched=0;

  WCOREPUSH;

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->MatchTmr));

  debug("CALLED match_random\n");

  nvtxs  = graph->nvtxs;
  ncon   = graph->ncon;
  xadj   = graph->xadj;
  vwgt   = graph->vwgt;
  adjncy = graph->adjncy;
  adjwgt = graph->adjwgt;
  cmap   = graph->cmap;

  maxvwgt  = ctrl->maxvwgt;

  match   = iset(nvtxs, UNMATCHED, iwspacemalloc(ctrl, nvtxs));
  perm    = iwspacemalloc(ctrl, nvtxs);
  tperm   = iwspacemalloc(ctrl, nvtxs);
  degrees = iwspacemalloc(ctrl, nvtxs);

  /* Determine a "random" traversal order that is biased towards 
     low-degree vertices */
  debug("Permuting %ld vertices with %ld shuffles\n", nvtxs, nvtxs/8);
  irandArrayPermute(nvtxs, tperm, nvtxs/8, 1);
  debug("Done permuting\n");

  avgdegree = 4.0*(xadj[nvtxs]/nvtxs);
  for (i=0; i<nvtxs; i++) {
    bnum = sqrt(1+xadj[i+1]-xadj[i]);
    degrees[i] = (bnum > avgdegree ? avgdegree : bnum);
  }
  BucketSortKeysInc(ctrl, nvtxs, avgdegree, degrees, tperm, perm);


  /* Traverse the vertices and compute the matching */
  for (cnvtxs=0, last_unmatched=0, pi=0; pi<nvtxs; pi++) {
    i = perm[pi];

    if (match[i] == UNMATCHED) {  /* Unmatched */
      maxidx = i;

      if ((ncon == 1 ? vwgt[i] < maxvwgt[0] : ivecle(ncon, vwgt+i*ncon, maxvwgt))) {
        /* Deal with island vertices. Find a non-island and match it with. 
           The matching ignores ctrl->maxvwgt requirements */
        if (xadj[i] == xadj[i+1]) {
          last_unmatched = gk_max(pi, last_unmatched)+1;
          for (; last_unmatched<nvtxs; last_unmatched++) {
            j = perm[last_unmatched];
            if (match[j] == UNMATCHED) {
              maxidx = j;
              break;
            }
          }
        }
        else {
          /* Find a random matching, subject to maxvwgt constraints */
          if (ncon == 1) {
            /* single constraint version */
            for (j=xadj[i]; j<xadj[i+1]; j++) {
              k = adjncy[j];
              if (match[k] == UNMATCHED && vwgt[i]+vwgt[k] <= maxvwgt[0]) {
                maxidx = k;
                break;
              }
            }

            /* If it did not match, record for a 2-hop matching. */
            if (maxidx == i && 2*vwgt[i] < maxvwgt[0]) {
              nunmatched++;
              maxidx = UNMATCHED;
            }
          }
          else {
            /* multi-constraint version */
            for (j=xadj[i]; j<xadj[i+1]; j++) {
              k = adjncy[j];
              if (match[k] == UNMATCHED && 
                  ivecaxpylez(ncon, 1, vwgt+i*ncon, vwgt+k*ncon, maxvwgt)) {
                maxidx = k;
                break;
              }
            }

            /* If it did not match, record for a 2-hop matching. */
            if (maxidx == i && ivecaxpylez(ncon, 2, vwgt+i*ncon, vwgt+i*ncon, maxvwgt)) {
              nunmatched++;
              maxidx = UNMATCHED;
            }
          }
        }
      }

      if (maxidx != UNMATCHED) {
        cmap[i]  = cmap[maxidx] = cnvtxs++;
        match[i] = maxidx;
        match[maxidx] = i;
      }
    }
  }

  //printf("nunmatched: %zu\n", nunmatched);

  debug("[LINE 184]\n");

  /* see if a 2-hop matching is required/allowed */
  if (!ctrl->no2hop && nunmatched > UNMATCHEDFOR2HOP*nvtxs) 
    cnvtxs = Match_2Hop(ctrl, graph, perm, match, cnvtxs, nunmatched);


  /* match the final unmatched vertices with themselves and reorder the vertices 
     of the coarse graph for memory-friendly contraction */
  for (cnvtxs=0, i=0; i<nvtxs; i++) {
    if (match[i] == UNMATCHED) {
      match[i] = i;
      cmap[i]  = cnvtxs++;
    }
    else {
      if (i <= match[i]) 
        cmap[i] = cmap[match[i]] = cnvtxs++;
    }
  }

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->MatchTmr));

  CreateCoarseGraph(ctrl, graph, cnvtxs, match);

  WCOREPOP;

  return cnvtxs;
}


/**************************************************************************/
/*! This function finds a matching using the HEM heuristic. The vertices 
    are visited based on increasing degree to ensure that all vertices are 
    given a chance to match with something. 
 */
/**************************************************************************/
idx_t Match_SHEM(ctrl_t *ctrl, graph_t *graph)
{
  idx_t i, pi, ii, j, jj, jjinc, k, nvtxs, ncon, cnvtxs, maxidx, maxwgt, 
        last_unmatched, avgdegree, bnum;
  idx_t *xadj, *vwgt, *adjncy, *adjwgt, *maxvwgt;
  idx_t *match, *cmap, *degrees, *perm, *tperm;
  size_t nunmatched=0;

  WCOREPUSH;

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->MatchTmr));

  debug("CALLED match_shem\n");

  nvtxs  = graph->nvtxs;
  ncon   = graph->ncon;
  xadj   = graph->xadj;
  vwgt   = graph->vwgt;
  adjncy = graph->adjncy;
  adjwgt = graph->adjwgt;
  cmap   = graph->cmap;

  maxvwgt  = ctrl->maxvwgt;

  match   = iset(nvtxs, UNMATCHED, iwspacemalloc(ctrl, nvtxs));
  perm    = iwspacemalloc(ctrl, nvtxs);
  tperm   = iwspacemalloc(ctrl, nvtxs);
  degrees = iwspacemalloc(ctrl, nvtxs);

  /* Determine a "random" traversal order that is biased towards low-degree vertices */
  irandArrayPermute(nvtxs, tperm, nvtxs/8, 1);

  avgdegree = 4.0*(xadj[nvtxs]/nvtxs);
  for (i=0; i<nvtxs; i++) {
    bnum = sqrt(1+xadj[i+1]-xadj[i]);
    degrees[i] = (bnum > avgdegree ? avgdegree : bnum);
  }
  BucketSortKeysInc(ctrl, nvtxs, avgdegree, degrees, tperm, perm);


  /* Traverse the vertices and compute the matching */
  for (cnvtxs=0, last_unmatched=0, pi=0; pi<nvtxs; pi++) {
    i = perm[pi];

    if (match[i] == UNMATCHED) {  /* Unmatched */
      maxidx = i;
      maxwgt = -1;

      if ((ncon == 1 ? vwgt[i] < maxvwgt[0] : ivecle(ncon, vwgt+i*ncon, maxvwgt))) {
        /* Deal with island vertices. Find a non-island and match it with. 
           The matching ignores ctrl->maxvwgt requirements */
        if (xadj[i] == xadj[i+1]) { 
          last_unmatched = gk_max(pi, last_unmatched)+1;
          for (; last_unmatched<nvtxs; last_unmatched++) {
            j = perm[last_unmatched];
            if (match[j] == UNMATCHED) {
              maxidx = j;
              break;
            }
          }
        }
        else {
          /* Find a heavy-edge matching, subject to maxvwgt constraints */
          if (ncon == 1) {
            /* single constraint version */
            for (j=xadj[i]; j<xadj[i+1]; j++) {
              k = adjncy[j];
              if (match[k] == UNMATCHED && 
                  maxwgt < adjwgt[j] && vwgt[i]+vwgt[k] <= maxvwgt[0]) {
                maxidx = k;
                maxwgt = adjwgt[j];
              }
            }

            /* If it did not match, record for a 2-hop matching. */
            if (maxidx == i && 2*vwgt[i] < maxvwgt[0]) {
              nunmatched++;
              maxidx = UNMATCHED;
            }
          }
          else {
            /* multi-constraint version */
            for (j=xadj[i]; j<xadj[i+1]; j++) {
              k = adjncy[j];
              if (match[k] == UNMATCHED && 
                  ivecaxpylez(ncon, 1, vwgt+i*ncon, vwgt+k*ncon, maxvwgt) &&
                  (maxwgt < adjwgt[j] || 
                   (maxwgt == adjwgt[j] && 
                    BetterVBalance(ncon, graph->invtvwgt, vwgt+i*ncon, 
                        vwgt+maxidx*ncon, vwgt+k*ncon)))) {
                maxidx = k;
                maxwgt = adjwgt[j];
              }
            }

            /* If it did not match, record for a 2-hop matching. */
            if (maxidx == i && ivecaxpylez(ncon, 2, vwgt+i*ncon, vwgt+i*ncon, maxvwgt)) {
              nunmatched++;
              maxidx = UNMATCHED;
            }
          }
        }
      }

      if (maxidx != UNMATCHED) {
        cmap[i]  = cmap[maxidx] = cnvtxs++;
        match[i] = maxidx;
        match[maxidx] = i;
      }
    }
  }

  //printf("nunmatched: %zu\n", nunmatched);

  /* see if a 2-hop matching is required/allowed */
  if (!ctrl->no2hop && nunmatched > UNMATCHEDFOR2HOP*nvtxs) 
    cnvtxs = Match_2Hop(ctrl, graph, perm, match, cnvtxs, nunmatched);


  /* match the final unmatched vertices with themselves and reorder the vertices 
     of the coarse graph for memory-friendly contraction */
  for (cnvtxs=0, i=0; i<nvtxs; i++) {
    if (match[i] == UNMATCHED) {
      match[i] = i;
      cmap[i] = cnvtxs++;
    }
    else {
      if (i <= match[i]) 
        cmap[i] = cmap[match[i]] = cnvtxs++;
    }
  }

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->MatchTmr));

  CreateCoarseGraph(ctrl, graph, cnvtxs, match);

  WCOREPOP;

  debug("EXITED match_shem\n");

  return cnvtxs;
}


/*************************************************************************/
/*! This function matches the unmatched vertices using a 2-hop matching 
    that involves vertices that are two hops away from each other. */
/**************************************************************************/
idx_t Match_2Hop(ctrl_t *ctrl, graph_t *graph, idx_t *perm, idx_t *match, 
          idx_t cnvtxs, size_t nunmatched)
{
  debug("CALLED match_two_hop\n");

  cnvtxs = Match_2HopAny(ctrl, graph, perm, match, cnvtxs, &nunmatched, 2);
  cnvtxs = Match_2HopAll(ctrl, graph, perm, match, cnvtxs, &nunmatched, 64);
  if (nunmatched > 1.5*UNMATCHEDFOR2HOP*graph->nvtxs) 
    cnvtxs = Match_2HopAny(ctrl, graph, perm, match, cnvtxs, &nunmatched, 3);
  if (nunmatched > 2.0*UNMATCHEDFOR2HOP*graph->nvtxs) 
    cnvtxs = Match_2HopAny(ctrl, graph, perm, match, cnvtxs, &nunmatched, graph->nvtxs);

  debug("EXITING match_two_hop\n");

  return cnvtxs;
}


/*************************************************************************/
/*! This function matches the unmatched vertices whose degree is less than
    maxdegree using a 2-hop matching that involves vertices that are two 
    hops away from each other. 
    The requirement of the 2-hop matching is a simple non-empty overlap
    between the adjancency lists of the vertices. */
/**************************************************************************/
idx_t Match_2HopAny(ctrl_t *ctrl, graph_t *graph, idx_t *perm, idx_t *match, 
          idx_t cnvtxs, size_t *r_nunmatched, size_t maxdegree)
{
  idx_t i, pi, ii, j, jj, k, nvtxs;
  idx_t *xadj, *adjncy, *colptr, *rowind;
  idx_t *cmap;
  size_t nunmatched;

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->Aux3Tmr));

  nvtxs  = graph->nvtxs;
  xadj   = graph->xadj;
  adjncy = graph->adjncy;
  cmap   = graph->cmap;

  nunmatched = *r_nunmatched;

  /*IFSET(ctrl->dbglvl, METIS_DBG_COARSEN, printf("IN: nunmatched: %zu\t", nunmatched)); */

  /* create the inverted index */
  WCOREPUSH;
  colptr = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs+1));
  for (i=0; i<nvtxs; i++) {
    if (match[i] == UNMATCHED && xadj[i+1]-xadj[i] < maxdegree) {
      for (j=xadj[i]; j<xadj[i+1]; j++)
        colptr[adjncy[j]]++;
    }
  }
  MAKECSR(i, nvtxs, colptr);

  rowind = iwspacemalloc(ctrl, colptr[nvtxs]);
  for (pi=0; pi<nvtxs; pi++) {
    i = perm[pi];
    if (match[i] == UNMATCHED && xadj[i+1]-xadj[i] < maxdegree) {
      for (j=xadj[i]; j<xadj[i+1]; j++)
        rowind[colptr[adjncy[j]]++] = i;
    }
  }
  SHIFTCSR(i, nvtxs, colptr);

  /* compute matchings by going down the inverted index */
  for (pi=0; pi<nvtxs; pi++) {
    i = perm[pi];
    if (colptr[i+1]-colptr[i] < 2)
      continue;

    for (jj=colptr[i+1], j=colptr[i]; j<jj; j++) {
      if (match[rowind[j]] == UNMATCHED) {
        for (jj--; jj>j; jj--) {
          if (match[rowind[jj]] == UNMATCHED) {
            cmap[rowind[j]] = cmap[rowind[jj]] = cnvtxs++;
            match[rowind[j]]  = rowind[jj];
            match[rowind[jj]] = rowind[j];
            nunmatched -= 2;
            break;
          }
        }
      }
    }
  }
  WCOREPOP;

  /*IFSET(ctrl->dbglvl, METIS_DBG_COARSEN, printf("OUT: nunmatched: %zu\n", nunmatched)); */

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->Aux3Tmr));

  *r_nunmatched = nunmatched;
  return cnvtxs;
}


/*************************************************************************/
/*! This function matches the unmatched vertices whose degree is less than
    maxdegree using a 2-hop matching that involves vertices that are two 
    hops away from each other. 
    The requirement of the 2-hop matching is that of identical adjacency
    lists.
 */
/**************************************************************************/
idx_t Match_2HopAll(ctrl_t *ctrl, graph_t *graph, idx_t *perm, idx_t *match, 
          idx_t cnvtxs, size_t *r_nunmatched, size_t maxdegree)
{
  idx_t i, pi, pk, ii, j, jj, k, nvtxs, mask, idegree;
  idx_t *xadj, *adjncy;
  idx_t *cmap, *mark;
  ikv_t *keys;
  size_t nunmatched, ncand;

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->Aux3Tmr));

  nvtxs  = graph->nvtxs;
  xadj   = graph->xadj;
  adjncy = graph->adjncy;
  cmap   = graph->cmap;

  nunmatched = *r_nunmatched;
  mask = IDX_MAX/maxdegree;

  /*IFSET(ctrl->dbglvl, METIS_DBG_COARSEN, printf("IN: nunmatched: %zu\t", nunmatched)); */

  WCOREPUSH;

  /* collapse vertices with identical adjancency lists */
  keys = ikvwspacemalloc(ctrl, nunmatched);
  for (ncand=0, pi=0; pi<nvtxs; pi++) {
    i = perm[pi];
    idegree = xadj[i+1]-xadj[i];
    if (match[i] == UNMATCHED && idegree > 1 && idegree < maxdegree) {
      for (k=0, j=xadj[i]; j<xadj[i+1]; j++) 
        k += adjncy[j]%mask;
      keys[ncand].val = i;
      keys[ncand].key = (k%mask)*maxdegree + idegree;
      ncand++;
    }
  }
  ikvsorti(ncand, keys);

  mark = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
  for (pi=0; pi<ncand; pi++) {
    i = keys[pi].val;
    if (match[i] != UNMATCHED)
      continue;

    for (j=xadj[i]; j<xadj[i+1]; j++)
      mark[adjncy[j]] = i;

    for (pk=pi+1; pk<ncand; pk++) {
      k = keys[pk].val;
      if (match[k] != UNMATCHED)
        continue;

      if (keys[pi].key != keys[pk].key)
        break;
      if (xadj[i+1]-xadj[i] != xadj[k+1]-xadj[k])
        break;

      for (jj=xadj[k]; jj<xadj[k+1]; jj++) {
        if (mark[adjncy[jj]] != i)
          break;
      }
      if (jj == xadj[k+1]) {
        cmap[i] = cmap[k] = cnvtxs++;
        match[i] = k;
        match[k] = i;
        nunmatched -= 2;
        break;
      }
    }
  }
  WCOREPOP;

  /*IFSET(ctrl->dbglvl, METIS_DBG_COARSEN, printf("OUT: ncand: %zu, nunmatched: %zu\n", ncand, nunmatched)); */

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->Aux3Tmr));

  *r_nunmatched = nunmatched;
  return cnvtxs;
}


/*************************************************************************/
/*! This function finds a matching by selecting an adjacent vertex based
    on the Jaccard coefficient of the adjaceny lists.
 */
/**************************************************************************/
idx_t Match_JC(ctrl_t *ctrl, graph_t *graph)
{
  idx_t i, pi, ii, iii, j, jj, jjj, jjinc, k, nvtxs, ncon, cnvtxs, maxidx, 
        last_unmatched, avgdegree, bnum;
  idx_t *xadj, *vwgt, *adjncy, *adjwgt, *maxvwgt;
  idx_t *match, *cmap, *degrees, *perm, *tperm, *vec, *marker;
  idx_t mytwgt, xtwgt, ctwgt;
  float bscore, score;

  WCOREPUSH;

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->MatchTmr));

  nvtxs  = graph->nvtxs;
  ncon   = graph->ncon;
  xadj   = graph->xadj;
  vwgt   = graph->vwgt;
  adjncy = graph->adjncy;
  adjwgt = graph->adjwgt;
  cmap   = graph->cmap;

  maxvwgt  = ctrl->maxvwgt;

  match   = iset(nvtxs, UNMATCHED, iwspacemalloc(ctrl, nvtxs));
  perm    = iwspacemalloc(ctrl, nvtxs);
  tperm   = iwspacemalloc(ctrl, nvtxs);
  degrees = iwspacemalloc(ctrl, nvtxs);

  irandArrayPermute(nvtxs, tperm, nvtxs/8, 1);

  avgdegree = 4.0*(xadj[nvtxs]/nvtxs);
  for (i=0; i<nvtxs; i++) {
    bnum = sqrt(1+xadj[i+1]-xadj[i]);
    degrees[i] = (bnum > avgdegree ? avgdegree : bnum);
  }
  BucketSortKeysInc(ctrl, nvtxs, avgdegree, degrees, tperm, perm);

  /* point to the wspace vectors that are not needed any more */
  vec    = tperm;
  marker = degrees;
  iset(nvtxs, -1, vec);
  iset(nvtxs, -1, marker);

  for (cnvtxs=0, last_unmatched=0, pi=0; pi<nvtxs; pi++) {
    i = perm[pi];

    if (match[i] == UNMATCHED) {  /* Unmatched */
      maxidx = i;

      if ((ncon == 1 ? vwgt[i] < maxvwgt[0] : ivecle(ncon, vwgt+i*ncon, maxvwgt))) {
        /* Deal with island vertices. Find a non-island and match it with. 
           The matching ignores ctrl->maxvwgt requirements */
        if (xadj[i] == xadj[i+1]) {
          last_unmatched = gk_max(pi, last_unmatched)+1;
          for (; last_unmatched<nvtxs; last_unmatched++) {
            j = perm[last_unmatched];
            if (match[j] == UNMATCHED) {
              maxidx = j;
              break;
            }
          }
        }
        else {
          if (ncon == 1) {
            /* Find a max JC pair, subject to maxvwgt constraints */
            if (xadj[i+1]-xadj[i] < avgdegree) {
              marker[i] = i;
              bscore = 0.0;
              mytwgt = 0;
              for (j=xadj[i]; j<xadj[i+1]; j++) {
                mytwgt += 1;//adjwgt[j];
                vec[adjncy[j]] = 1;//adjwgt[j];
              }

              /* single constraint pairing */
#ifdef XXX
              for (j=xadj[i]; j<xadj[i+1]; j++) {
                ii = adjncy[j];
                if (marker[ii] == i || match[ii] != UNMATCHED || vwgt[i]+vwgt[ii] > maxvwgt[0])
                  continue;

                ctwgt = xtwgt = 0;
                for (jj=xadj[ii]; jj<xadj[ii+1]; jj++) {
                  xtwgt += adjwgt[jj];
                  if (vec[adjncy[jj]] > 0)
                    ctwgt += vec[adjncy[jj]] + adjwgt[jj];
                  else if (adjncy[jj] == i) {
                    ctwgt += adjwgt[jj];
                    xtwgt -= adjwgt[jj];
                  }
                }

                score = 1.0*ctwgt/(mytwgt+xtwgt-ctwgt);
                if (score > bscore) {
                  bscore = score;
                  maxidx = ii;
                }
                marker[ii] = i;
              }
#endif

              for (j=xadj[i]; j<xadj[i+1]; j++) {
                ii = adjncy[j];
                for (jj=xadj[ii]; jj<xadj[ii+1]; jj++) {
                  iii = adjncy[jj];
  
                  if (marker[iii] == i || match[iii] != UNMATCHED || vwgt[i]+vwgt[iii] > maxvwgt[0])
                    continue;
  
                  ctwgt = xtwgt = 0;
                  for (jjj=xadj[iii]; jjj<xadj[iii+1]; jjj++) {
                    xtwgt += 1;//adjwgt[jjj];
                    if (vec[adjncy[jjj]] > 0)
                      ctwgt += 2;//vec[adjncy[jjj]] + adjwgt[jjj];
                    else if (adjncy[jjj] == i) 
                      ctwgt += 10*adjwgt[jjj];
                  }
  
                  score = 1.0*ctwgt/(mytwgt+xtwgt);
                  //printf("%"PRIDX" %"PRIDX" %"PRIDX" %.4f\n", mytwgt, xtwgt, ctwgt, score);
                  if (score > bscore) {
                    bscore = score;
                    maxidx = iii;
                  }
                  marker[iii] = i;
                }
              }
  
              /* reset vec array */
              for (j=xadj[i]; j<xadj[i+1]; j++) 
                vec[adjncy[j]] = -1;
            }
          }
          else {
            /* multi-constraint version */
            for (j=xadj[i]; j<xadj[i+1]; j++) {
              k = adjncy[j];
              if (match[k] == UNMATCHED && 
                  ivecaxpylez(ncon, 1, vwgt+i*ncon, vwgt+k*ncon, maxvwgt)) {
                maxidx = k;
                break;
              }
            }
          }
        }
      }

      if (maxidx != UNMATCHED) {
        cmap[i]  = cmap[maxidx] = cnvtxs++;
        match[i] = maxidx;
        match[maxidx] = i;
      }
    }
  }


  /* match the final unmatched vertices with themselves and reorder the vertices 
     of the coarse graph for memory-friendly contraction */
  for (cnvtxs=0, i=0; i<nvtxs; i++) {
    if (match[i] == UNMATCHED) {
      match[i] = i;
      cmap[i]  = cnvtxs++;
    }
    else {
      if (i <= match[i]) 
        cmap[i] = cmap[match[i]] = cnvtxs++;
    }
  }

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->MatchTmr));

  CreateCoarseGraph(ctrl, graph, cnvtxs, match);

  WCOREPOP;

  return cnvtxs;
}


/*************************************************************************/
/*! This function prints various stats for each graph during coarsening 
 */
/*************************************************************************/
void PrintCGraphStats(ctrl_t *ctrl, graph_t *graph)
{
  idx_t i;

  printf("%10"PRIDX" %10"PRIDX" %10"PRIDX" [%"PRIDX"] [", 
      graph->nvtxs, graph->nedges, isum(graph->nedges, graph->adjwgt, 1), ctrl->CoarsenTo);

  for (i=0; i<graph->ncon; i++)
    printf(" %8"PRIDX":%8"PRIDX, ctrl->maxvwgt[i], graph->tvwgt[i]);
  printf(" ]\n");
}


/*************************************************************************/
/*! This function creates the coarser graph. Depending on the size of the
    candidate adjancency lists it either uses a hash table or an array
    to do duplicate detection.
 */
/*************************************************************************/
void CreateCoarseGraph(ctrl_t *ctrl, graph_t *graph, idx_t cnvtxs, 
         idx_t *match)
{
  debug("CreateCoarseGraph!!!\n");
  #if DEBUG_COARSEN
  PrintGraph(graph);
  debug("\n");
  #endif
  debug("coarse_n: %ld\n", cnvtxs);
  debug("matches: [");
  for (int i = 0; i < graph->nvtxs; i++) {
    debug("Matched(%ld), ", match[i]);
  }
  debug("]\n");
  debug("coarsening: [");
  for (int i = 0; i < graph->nvtxs; i++) {
    debug("%ld, ", graph->cmap[i]);
  }
  debug("]\n");
  idx_t j, jj, k, kk, l, m, istart, iend, nvtxs, nedges, ncon, 
        cnedges, v, u, mask;
  idx_t *xadj, *vwgt, *vsize, *adjncy, *adjwgt;
  idx_t *cmap, *htable, *dtable;
  idx_t *cxadj, *cvwgt, *cvsize, *cadjncy, *cadjwgt;
  graph_t *cgraph;
  int dovsize, dropedges;
  idx_t cv, nkeep, droppedewgt;
  idx_t *keys=NULL, *medianewgts=NULL, *noise=NULL;

  WCOREPUSH;

  dovsize   = (ctrl->objtype == METIS_OBJTYPE_VOL ? 1 : 0);
  dropedges = ctrl->dropedges;

  mask = HTLENGTH;

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->ContractTmr));

  nvtxs   = graph->nvtxs;
  ncon    = graph->ncon;
  xadj    = graph->xadj;
  vwgt    = graph->vwgt;
  vsize   = graph->vsize;
  adjncy  = graph->adjncy;
  adjwgt  = graph->adjwgt;
  cmap    = graph->cmap;

  /* Setup structures for dropedges */
  if (dropedges) {
    for (nkeep=-1, v=0; v<nvtxs; v++) 
      nkeep = gk_max(nkeep, xadj[v+1]-xadj[v]);

    medianewgts = iwspacemalloc(ctrl, cnvtxs);
    noise       = iwspacemalloc(ctrl, cnvtxs);
    keys        = iwspacemalloc(ctrl, 2*(nkeep+1));

    for (v=0; v<cnvtxs; v++) 
      noise[v] = irandInRange(128);
  }

  /* Initialize the coarser graph */
  cgraph   = SetupCoarseGraph(graph, cnvtxs, dovsize);
  cxadj    = cgraph->xadj;
  cvwgt    = cgraph->vwgt;
  cvsize   = cgraph->vsize;
  cadjncy  = cgraph->adjncy;
  cadjwgt  = cgraph->adjwgt;

  // for determinism
  cadjwgt[0] = -1;

  htable = iset(mask+1, -1, iwspacemalloc(ctrl, mask+1));   /* hash table */
  dtable = iset(cnvtxs, -1, iwspacemalloc(ctrl, cnvtxs));   /* direct table */

  cxadj[0] = cnvtxs = cnedges = 0;
  for (v=0; v<nvtxs; v++) {
    if ((u = match[v]) < v)
      continue;

    ASSERT(cmap[v] == cnvtxs);
    ASSERT(cmap[match[v]] == cnvtxs);

    /* take care of the vertices */
    if (ncon == 1)
      cvwgt[cnvtxs] = vwgt[v];
    else
      icopy(ncon, vwgt+v*ncon, cvwgt+cnvtxs*ncon);

    if (dovsize)
      cvsize[cnvtxs] = vsize[v];

    if (v != u) { 
      if (ncon == 1)
        cvwgt[cnvtxs] += vwgt[u];
      else
        iaxpy(ncon, 1, vwgt+u*ncon, 1, cvwgt+cnvtxs*ncon, 1);

      if (dovsize)
        cvsize[cnvtxs] += vsize[u];
    }


    /* take care of the edges */ 
    if ((xadj[v+1]-xadj[v] + xadj[u+1]-xadj[u]) < (mask>>2)) { /* use mask */
      /* put the ID of the contracted node itself at the start, so that it can be 
       * removed easily */
      htable[cnvtxs&mask] = 0;
      cadjncy[0] = cnvtxs;
      nedges = 1;

      istart = xadj[v];
      iend   = xadj[v+1];
      for (j=istart; j<iend; j++) {
        k = cmap[adjncy[j]];
        for (kk=k&mask; htable[kk]!=-1 && cadjncy[htable[kk]]!=k; kk=((kk+1)&mask));
        debug("hash_table: [");
        for (int i = 0; i < mask + 1; i++) {
          if (htable[i] < 0) continue;
          debug("(%d, %ld), ", i, htable[i]);
        }
        debug("]\n");
        if ((m = htable[kk]) == -1) {
          debug("Adding at %ld with weight %ld\n", nedges, adjwgt[j]);
          cadjncy[nedges] = k;
          cadjwgt[nedges] = adjwgt[j];
          htable[kk] = nedges++;
        }
        else {
          debug("Incrementing %ld (%ld) with weight %ld\n", m, cadjwgt[m], adjwgt[j]);
          cadjwgt[m] += adjwgt[j];
        }
      }

      debug("ca: [");
      for (int i = 0; i < cnedges + nedges; i++) {
        debug("%ld, ", cgraph->adjncy[i]);
      }
      debug("]\n");
      debug("ca_w: [");
      for (int i = 0; i < cnedges + nedges; i++) {
        debug("%ld, ", cgraph->adjwgt[i]);
      }
      debug("]\n");
      debug("hash_table: [");
      for (int i = 0; i < mask + 1; i++) {
        if (htable[i] < 0) continue;
        debug("(%d, %ld), ", i, htable[i]);
      }
      debug("]\n");
  
  
      if (v != u) { 
        istart = xadj[u];
        iend   = xadj[u+1];
        for (j=istart; j<iend; j++) {
          k = cmap[adjncy[j]];
          for (kk=k&mask; htable[kk]!=-1 && cadjncy[htable[kk]]!=k; kk=((kk+1)&mask));
          if ((m = htable[kk]) == -1) {
            debug("Setting last weight to %ld\n", adjwgt[j]);
            cadjncy[nedges] = k;
            cadjwgt[nedges] = adjwgt[j];
            htable[kk]      = nedges++;
          }
          else {
            cadjwgt[m] += adjwgt[j];
          }
        }
      }

      /* zero out the htable */
      debug("zeroing\n");
      for (j=0; j<nedges; j++) {
        k = cadjncy[j];
        debug("k: %ld\n", k);
        for (kk=k&mask; cadjncy[htable[kk]]!=k; kk=((kk+1)&mask)) {
          debug("kk: %ld, htable: %ld, cadj: %ld\n", kk, htable[kk], cadjncy[htable[kk]]);
        }
        htable[kk] = -1;  
      }
      debug("Zeroed\n");

      /* remove the contracted vertex from the list */
      cadjncy[0] = cadjncy[--nedges];
      cadjwgt[0] = cadjwgt[nedges];
    }
    else {
      nedges = 0;
      istart = xadj[v];
      iend   = xadj[v+1];
      for (j=istart; j<iend; j++) {
        k = cmap[adjncy[j]];
        if ((m = dtable[k]) == -1) {
          cadjncy[nedges] = k;
          cadjwgt[nedges] = adjwgt[j];
          dtable[k] = nedges++;
        }
        else {
          cadjwgt[m] += adjwgt[j];
        }
      }

      if (v != u) { 
        istart = xadj[u];
        iend   = xadj[u+1];
        for (j=istart; j<iend; j++) {
          k = cmap[adjncy[j]];
          if ((m = dtable[k]) == -1) {
            cadjncy[nedges] = k;
            cadjwgt[nedges] = adjwgt[j];
            dtable[k] = nedges++;
          }
          else {
            cadjwgt[m] += adjwgt[j];
          }
        }

        /* Remove the contracted self-loop, when present */
        if ((j = dtable[cnvtxs]) != -1) {
          ASSERT(cadjncy[j] == cnvtxs);
          cadjncy[j]        = cadjncy[--nedges];
          cadjwgt[j]        = cadjwgt[nedges];
          dtable[cnvtxs] = -1;
        }
      }

      /* Zero out the dtable */
      for (j=0; j<nedges; j++)
        dtable[cadjncy[j]] = -1;  
    }


    /* Determine the median weight of the incident edges, which will be used
       to keep an edge (u, v) iff wgt(u, v) >= min(medianewgts[u], medianewgts[v]) */
    if (dropedges) {
      for (j=0; j<nedges; j++) 
        keys[j] = (cadjwgt[j]<<8) + noise[cnvtxs] + noise[cadjncy[j]];
      isortd(nedges, keys);
      medianewgts[cnvtxs] = keys[((xadj[v+1]-xadj[v] + xadj[u+1]-xadj[u])>>1)];
    }

    cadjncy         += nedges;
    cadjwgt         += nedges;
    cnedges         += nedges;
    cxadj[++cnvtxs]  = cnedges;
  }

  /* compact the adjacency structure of the coarser graph to keep only +ve edges */
  if (dropedges) { 
    droppedewgt = 0;

    cadjncy  = cgraph->adjncy;
    cadjwgt  = cgraph->adjwgt;

    cnedges = 0;
    for (u=0; u<cnvtxs; u++) {
      istart = cxadj[u];
      iend   = cxadj[u+1];
      for (j=istart; j<iend; j++) {
        v = cadjncy[j];
        if ((cadjwgt[j]<<8) + noise[u] + noise[v] >= gk_min(medianewgts[u], medianewgts[v])) {
          cadjncy[cnedges]   = cadjncy[j];
          cadjwgt[cnedges++] = cadjwgt[j];
        }
        else 
          droppedewgt += cadjwgt[j];
      }
      cxadj[u] = cnedges;
    }
    SHIFTCSR(j, cnvtxs, cxadj);

    //printf("droppedewgt: %ld\n", (int)droppedewgt);

    cgraph->droppedewgt = droppedewgt;
  }

  cgraph->nedges = cnedges;

  for (j=0; j<ncon; j++) {
    cgraph->tvwgt[j]    = isum(cgraph->nvtxs, cgraph->vwgt+j, ncon);
    cgraph->invtvwgt[j] = 1.0/(cgraph->tvwgt[j] > 0 ? cgraph->tvwgt[j] : 1);
  }

  ReAdjustMemory(ctrl, graph, cgraph);

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->ContractTmr));

  WCOREPOP;
}


/*************************************************************************/
/*! Setup the various arrays for the coarse graph 
 */
/*************************************************************************/
graph_t *SetupCoarseGraph(graph_t *graph, idx_t cnvtxs, int dovsize)
{
  graph_t *cgraph;

  cgraph = CreateGraph();

  cgraph->nvtxs = cnvtxs;
  cgraph->ncon  = graph->ncon;

  cgraph->finer  = graph;
  graph->coarser = cgraph;

  /* Allocate memory for the coarser graph.
     NOTE: The +1 in the adjwgt/adjncy is to allow the optimization of self-loop
           detection by adding ahead of time the self-loop. That optimization
           requires a +1 adjncy/adjwgt array for the limit case where the 
           coarser graph is of the same size of the previous graph. */
  cgraph->xadj     = imalloc(cnvtxs+1, "SetupCoarseGraph: xadj");
  cgraph->adjncy   = imalloc(graph->nedges+1,   "SetupCoarseGraph: adjncy");
  cgraph->adjwgt   = imalloc(graph->nedges+1,   "SetupCoarseGraph: adjwgt");
  cgraph->vwgt     = imalloc(cgraph->ncon*cnvtxs, "SetupCoarseGraph: vwgt");
  cgraph->tvwgt    = imalloc(cgraph->ncon, "SetupCoarseGraph: tvwgt");
  cgraph->invtvwgt = rmalloc(cgraph->ncon, "SetupCoarseGraph: invtvwgt");

  if (dovsize)
    cgraph->vsize = imalloc(cnvtxs,   "SetupCoarseGraph: vsize");

  return cgraph;
}


/*************************************************************************/
/*! This function re-adjusts the amount of memory that was allocated if
    it will lead to significant savings 
 */
/*************************************************************************/
void ReAdjustMemory(ctrl_t *ctrl, graph_t *graph, graph_t *cgraph) 
{
  if (cgraph->nedges > 10000 && cgraph->nedges < 0.9*graph->nedges) {
    cgraph->adjncy = irealloc(cgraph->adjncy, cgraph->nedges, "ReAdjustMemory: adjncy");
    cgraph->adjwgt = irealloc(cgraph->adjwgt, cgraph->nedges, "ReAdjustMemory: adjwgt");
  }
}
