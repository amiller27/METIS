/*
 * mmd.c
 *
 * **************************************************************
 * The following C function was developed from a FORTRAN subroutine
 * in SPARSPAK written by Eleanor Chu, Alan George, Joseph Liu
 * and Esmond Ng.
 * 
 * The FORTRAN-to-C transformation and modifications such as dynamic
 * memory allocation and deallocation were performed by Chunguang
 * Sun.
 * ************************************************************** 
 *
 * Taken from SMMS, George 12/13/94
 *
 * The meaning of invperm, and perm vectors is different from that
 * in genqmd_ of SparsPak
 *
 * $Id: mmd.c 22385 2019-06-03 22:08:48Z karypis $
 */

#include "metislib.h"

#define PRINT_LIST(...) _PRINT_LIST(__VA_ARGS__, DEBUG_MMD)
#if DEBUG_MMD
#define debug(...) fprintf(stderr, __VA_ARGS__)
#else
#define debug(...)
#endif

void PrintMutableGraph(idx_t neqns, idx_t* xadj, idx_t* adjncy) {
  debug("MutableGraph { adjacency: [");
  for (int i = 1; i <= neqns; i++) {
    debug("[");
    for (int j = xadj[i]; j < xadj[i + 1]; j++) {
      debug("%ld", adjncy[j] - 1);
      if (j < xadj[i+1] - 1) {
        debug(", ");
      }
    }
    debug("]");
    if (i < neqns) {
      debug(", ");
    }
  }
  debug("] }\n");
}

void PrintFwdPtrList(idx_t neqns, idx_t* list) {
  debug("[");
  for (int i = 1; i <= neqns; i++) {
    if (list[i] == 0) {
      debug("None");
    } else if (list[i] > 0) {
      debug("Next(%ld)", list[i] - 1);
    } else {
      debug("NextNeg(%ld)", -list[i] - 1);
    }

    if (i != neqns) {
      debug(", ");
    }
  }
  debug("]\n");
}

void PrintHead(idx_t neqns, idx_t* head) {
  debug("head: ");
  PrintFwdPtrList(neqns, head);
}

void PrintForward(idx_t neqns, idx_t* forward) {
  debug("forward: ");
  PrintFwdPtrList(neqns, forward);
}

void PrintBackward(idx_t neqns, idx_t* backward, idx_t maxint) {
  debug("backward: [");
  for (int i = 1; i <= neqns; i++) {
    if (backward[i] == 0) {
      debug("None");
    } else if (backward[i] == -maxint) {
      debug("NegMaxInt");
    } else if (backward[i] > 0) {
      debug("Previous(%ld)", backward[i] - 1);
    } else {
      debug("Degree(%ld)", -backward[i] - 1);
    }

    if (i != neqns) {
      debug(", ");
    }
  }
  debug("]\n");
}

/*************************************************************************
*  genmmd  -- multiple minimum external degree
*  purpose -- this routine implements the minimum degree
*     algorithm. it makes use of the implicit representation
*     of elimination graphs by quotient graphs, and the notion
*     of indistinguishable nodes. It also implements the modifications
*     by multiple elimination and minimum external degree.
*     Caution -- the adjacency vector adjncy will be destroyed.
*  Input parameters --
*     neqns -- number of equations.
*     (xadj, adjncy) -- the adjacency structure.
*     delta  -- tolerance value for multiple elimination.
*     maxint -- maximum machine representable (short) integer
*               (any smaller estimate will do) for marking nodes.
*  Output parameters --
*     perm -- the minimum degree ordering.
*     invp -- the inverse of perm.
*     *ncsub -- an upper bound on the number of nonzero subscripts
*               for the compressed storage scheme.
*  Working parameters --
*     head -- vector for head of degree lists.
*     invp  -- used temporarily for degree forward link.
*     perm  -- used temporarily for degree backward link.
*     qsize -- vector for size of supernodes.
*     list -- vector for temporary linked lists.
*     marker -- a temporary marker vector.
*  Subroutines used -- mmdelm, mmdint, mmdnum, mmdupd.
**************************************************************************/
void genmmd(idx_t neqns, idx_t *xadj, idx_t *adjncy, idx_t *invp, idx_t *perm,
     idx_t delta, idx_t *head, idx_t *qsize, idx_t *list, idx_t *marker,
     idx_t maxint, idx_t *ncsub)
{
    idx_t  ehead, i, mdeg, mdlmt, mdeg_node, nextmd, num, tag;

    debug("HERE BE DRAGONS\n");
    debug("THIS IS NOT A PLACE OF HONOR\n");

    if (neqns <= 0)  
      return;

    /* Adjust from C to Fortran */
    xadj--; adjncy--; invp--; perm--; head--; qsize--; list--; marker--;

    PrintMutableGraph(neqns, xadj, adjncy);

    /* initialization for the minimum degree algorithm. */
    *ncsub = 0;
    mmdint(neqns, xadj, adjncy, head, invp, perm, qsize, list, marker);

    /*  'num' counts the number of ordered nodes plus 1. */
    num = 1;

    /* eliminate all isolated nodes. */
    nextmd = head[1];
    while (nextmd > 0) {
      debug("nextmd: %ld\n", nextmd - 1);
      mdeg_node = nextmd;
      nextmd = invp[mdeg_node];
      marker[mdeg_node] = maxint;
      invp[mdeg_node] = -num;
      num = num + 1;
    }

    /* search for node of the minimum degree. 'mdeg' is the current */
    /* minimum degree; 'tag' is used to facilitate marking nodes.   */
    if (num > neqns) 
      goto n1000;
    tag = 1;
    head[1] = 0;
    mdeg = 2;

    /* infinite loop here ! */
    int aaron_i = 0;
    while (1) {
      debug("LOOP %d ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n", aaron_i++);
      // PrintMutableGraph(neqns, xadj, adjncy);
      PrintHead(neqns, head);
      PrintForward(neqns, invp);
      PrintBackward(neqns, perm, maxint);
      //PRINT_LIST(qsize, neqns);
      //PRINT_LIST(marker, neqns);
      debug("n_ordered_nodes: %ld\n", num - 1);
      // if (nextmd == 0) {
      //   debug("next_minimum_degree_node: None\n");
      // } else {
      //   debug("next_minimum_degree_node: %ld\n", nextmd);
      // }
      debug("tag: %ld\n", tag);
      debug("minimum_degree: %ld\n", mdeg);

      while (head[mdeg] <= 0) {
        debug("78 Incremented minimum_degree\n");
        mdeg++;
      }

      /* use value of 'delta' to set up 'mdlmt', which governs */
      /* when a degree update is to be performed.              */
      mdlmt = mdeg + delta;
      ehead = 0;

n500:
      PrintHead(neqns, head);
      mdeg_node = head[mdeg];
      debug("minimum degree start: %ld\n", mdeg);
      while (mdeg_node <= 0) {
        debug("94 Incremented minimum_degree\n");
        mdeg++;

        if (mdeg > mdlmt) 
          goto n900;
        mdeg_node = head[mdeg];
      };

      // debug("post loop: %ld\n", mdeg);

      /*  remove 'mdeg_node' from the degree structure. */
      nextmd = invp[mdeg_node];
      if (nextmd == 0) {
        debug("115 Set head %ld to None\n", mdeg - 1);
      } else if (nextmd > 0) {
        debug("115 Set head %ld to Next(%ld)\n", mdeg - 1, nextmd - 1);
      } else {
        debug("115 Set head %ld to NextNeg(%ld)\n", mdeg - 1, -nextmd - 1);
      }
      head[mdeg] = nextmd;
      if (nextmd > 0) {
        debug("118 Set perm %ld to Degree(%ld)\n", nextmd - 1, mdeg - 1);
        perm[nextmd] = -mdeg;
      }
      invp[mdeg_node] = -num;
      *ncsub += mdeg + qsize[mdeg_node] - 2;
      if ((num+qsize[mdeg_node]) > neqns)  
        goto n1000;

      /*  eliminate 'mdeg_node' and perform quotient graph */
      /*  transformation. reset 'tag' value if necessary.    */
      tag++;
      if (tag >= maxint) {
        tag = 1;
        for (i = 1; i <= neqns; i++)
          if (marker[i] < maxint)  
            marker[i] = 0;
      };

      debug("ENTER ELIMINATE\n");
      mmdelm(mdeg_node, xadj, adjncy, head, invp, perm, qsize, list, marker, maxint, tag, neqns);
      debug("EXIT ELIMINATE\n");

      num += qsize[mdeg_node];
      list[mdeg_node] = ehead;
      ehead = mdeg_node;
      if (delta >= 0) 
        goto n500;

 n900:
      /* update degrees of the nodes involved in the  */
      /* minimum degree nodes elimination.            */
      if (num > neqns)  
        goto n1000;
      debug("ENTER UPDATE\n");
      mmdupd( ehead, neqns, xadj, adjncy, delta, &mdeg, head, invp, perm, qsize, list, marker, maxint, &tag);
      debug("Updated minimum_degree to %ld\n", mdeg);
      debug("EXIT UPDATE\n");
    }; /* end of -- while ( 1 ) -- */

n1000:
    mmdnum( neqns, perm, invp, qsize );

    /* Adjust from Fortran back to C*/
    xadj++; adjncy++; invp++; perm++; head++; qsize++; list++; marker++;
}


/**************************************************************************
*           mmdelm ...... multiple minimum degree elimination
* Purpose -- This routine eliminates the node mdeg_node of minimum degree
*     from the adjacency structure, which is stored in the quotient
*     graph format. It also transforms the quotient graph representation
*     of the elimination graph.
* Input parameters --
*     mdeg_node -- node of minimum degree.
*     maxint -- estimate of maximum representable (short) integer.
*     tag    -- tag value.
* Updated parameters --
*     (xadj, adjncy) -- updated adjacency structure.
*     (head, forward, backward) -- degree doubly linked structure.
*     qsize -- size of supernode.
*     marker -- marker vector.
*     list -- temporary linked list of eliminated nabors.
***************************************************************************/
void mmdelm(idx_t mdeg_node, idx_t *xadj, idx_t *adjncy, idx_t *head, idx_t *forward,
     idx_t *backward, idx_t *qsize, idx_t *list, idx_t *marker, idx_t maxint, idx_t tag, idx_t neqns)
{
    idx_t   element, i,   istop, istart, j,
          jstop, jstart, link,
          nabor, node, npv, nqnbrs, nxnode,
          pvnode, rlmt, rloc, rnode, xqnbr;
    debug("---------- AT START OF ELIMINATE -------------\n");
    debug("minimum_degree_node: %ld\n", mdeg_node - 1);
    // PrintMutableGraph(neqns, xadj, adjncy);
    PrintHead(neqns, head);
    PrintForward(neqns, forward);
    PrintBackward(neqns, backward, IDX_MAX);
    // PRINT_LIST(qsize, neqns);
    // PRINT_LIST(marker, neqns);
    debug("tag: %ld\n", tag);
    debug("------------ END START OF ELIMINATE --------------\n");

    /* find the reachable set of 'mdeg_node' and */
    /* place it in the data structure.           */
    debug("215 Setting marker [%ld] to tag Tag(%ld)\n", mdeg_node - 1, tag);
    marker[mdeg_node] = tag;
    istart = xadj[mdeg_node];
    istop = xadj[mdeg_node+1] - 1;

    /* 'element' points to the beginning of the list of  */
    /* eliminated nabors of 'mdeg_node', and 'rloc' gives the */
    /* storage location for the next reachable node.   */
    element = 0;
    rloc = istart;
    rlmt = istop;
    debug("278 Finding neighbors of %ld\n", mdeg_node - 1);
    for ( i = istart; i <= istop; i++ ) {
        nabor = adjncy[i];
        if ( nabor == 0 ) break;
        debug("Looking at marker %ld %ld %ld\n", nabor - 1, marker[nabor], tag);
        if ( marker[nabor] < tag ) {
           debug("230 Setting marker [%ld] to tag Tag(%ld)\n", nabor - 1, tag);
           marker[nabor] = tag;
           if ( forward[nabor] < 0 )  {
              list[nabor] = element;
              element = nabor;
           } else {
              debug("297 Keeping neighbor %ld\n", nabor - 1);
              adjncy[rloc] = nabor;
              rloc++;
           };
        }; /* end of -- if -- */
    }; /* end of -- for -- */

  /* merge with reachable nodes from generalized elements. */
  while ( element > 0 ) {
      adjncy[rlmt] = -element;
      link = element;

n400:
      jstart = xadj[link];
      jstop = xadj[link+1] - 1;
      for ( j = jstart; j <= jstop; j++ ) {
          node = adjncy[j];
          link = -node;
          if ( node < 0 )  goto n400;
          if ( node == 0 ) break;
          if ((marker[node]<tag)&&(forward[node]>=0)) {
             debug("256 Setting marker [%ld] to tag Tag(%ld)\n", node - 1, tag);
             marker[node] = tag;
             /*use storage from eliminated nodes if necessary.*/
             while ( rloc >= rlmt ) {
                   link = -adjncy[rlmt];
                   rloc = xadj[link];
                   rlmt = xadj[link+1] - 1;
             };
            debug("320 Keeping neighbor %ld\n", node - 1);
             adjncy[rloc] = node;
             rloc++;
          };
      }; /* end of -- for ( j = jstart; -- */
      element = list[element];
    };  /* end of -- while ( element > 0 ) -- */
    if ( rloc <= rlmt ) {
      // debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
      // debug("310 Set adjncy %ld to 0\n", rloc);
      // debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
      adjncy[rloc] = 0;
    }
    /* for each node in the reachable set, do the following. */
    link = mdeg_node;

n1100:
    istart = xadj[link];
    istop = xadj[link+1] - 1;
    for ( i = istart; i <= istop; i++ ) {
        rnode = adjncy[i];
        link = -rnode;
        if ( rnode < 0 ) goto n1100;
        if ( rnode == 0 ) return;

        /* 'rnode' is in the degree list structure. */
        pvnode = backward[rnode];
        if (( pvnode != 0 ) && ( pvnode != (-maxint) )) {
           /* then remove 'rnode' from the structure. */
           nxnode = forward[rnode];
           if ( nxnode > 0 ) {
             if (pvnode > 0) {
               debug("348 Set backward %ld to Previous(%ld)\n", nxnode - 1, pvnode - 1);
             } else {
               debug("348 Set backward %ld to Degree(%ld)\n", nxnode - 1, -pvnode - 1);
             }
             backward[nxnode] = pvnode;
           }
           if ( pvnode > 0 ) forward[pvnode] = nxnode;
           npv = -pvnode;
           if ( pvnode < 0 ) {
              if (nxnode == 0) {
                debug("356 Set head %ld to None\n", npv - 1);
              } else if (nxnode > 0) {
                debug("356 Set head %ld to Next(%ld)\n", npv - 1, nxnode - 1);
              } else {
                debug("356 Set head %ld to NextNeg(%ld)\n", npv - 1, -nxnode - 1);
              }
             head[npv] = nxnode;
           }
        };

        /* purge inactive quotient nabors of 'rnode'. */
        jstart = xadj[rnode];
        jstop = xadj[rnode+1] - 1;
        xqnbr = jstart;
        for ( j = jstart; j <= jstop; j++ ) {
            nabor = adjncy[j];
            if ( nabor == 0 ) break;
            if ( marker[nabor] < tag ) {
                adjncy[xqnbr] = nabor;
                xqnbr++;
            };
        };

        /* no active nabor after the purging. */
        nqnbrs = xqnbr - jstart;
        if ( nqnbrs <= 0 ) {
           /* merge 'rnode' with 'mdeg_node'. */
           qsize[mdeg_node] += qsize[rnode];
           qsize[rnode] = 0;
           debug("313 Setting marker [%ld] to Maxint\n", rnode - 1);
           marker[rnode] = maxint;
           forward[rnode] = -mdeg_node;
           backward[rnode] = -maxint;
        } else {
           /* flag 'rnode' for degree update, and  */
           /* add 'mdeg_node' as a nabor of 'rnode'.      */
           forward[rnode] = nqnbrs + 1;
           backward[rnode] = 0;
           adjncy[xqnbr] = mdeg_node;
           xqnbr++;
           if ( xqnbr <= jstop ) {
             // debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
             // debug("372 Set adjncy %ld to 0 for rnode %ld\n", xqnbr, rnode);
             // debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
              adjncy[xqnbr] = 0;
           }
        };
      }; /* end of -- for ( i = istart; -- */
      return;
 }

/***************************************************************************
*    mmdint ---- mult minimum degree initialization
*    purpose -- this routine performs initialization for the
*       multiple elimination version of the minimum degree algorithm.
*    input parameters --
*       neqns  -- number of equations.
*       (xadj, adjncy) -- adjacency structure.
*    output parameters --
*       (head, dfrow, backward) -- degree doubly linked structure.
*       qsize -- size of supernode ( initialized to one).
*       list -- linked list.
*       marker -- marker vector.
****************************************************************************/
idx_t  mmdint(idx_t neqns, idx_t *xadj, idx_t *adjncy, idx_t *head, idx_t *forward,
     idx_t *backward, idx_t *qsize, idx_t *list, idx_t *marker)
{
    idx_t  fnode, ndeg, node;

    for ( node = 1; node <= neqns; node++ ) {
        head[node] = 0;
        qsize[node] = 1;
        marker[node] = 0;
        list[node] = 0;
    };

    /* initialize the degree doubly linked lists. */
    for ( node = 1; node <= neqns; node++ ) {
        // The following is something that Olaf Schenk identified as potentially a
        // bug that I introduced in the original code. For now, I reverted back
        // to the original code until I have some time to check.
        // ndeg = xadj[node+1] - xadj[node]/* + 1*/;   /* george */
        ndeg = xadj[node+1] - xadj[node] + 1;
        if (ndeg == 0)
          ndeg = 1;
        fnode = head[ndeg];
        forward[node] = fnode;
        head[ndeg] = node;
        if ( fnode > 0 ) { debug("230 Set backward %ld to Previous(%ld)\n", fnode - 1, node - 1); backward[fnode] = node; }
        debug("233 Set backward %ld to Degree(%ld)\n", node - 1, ndeg - 1);
        backward[node] = -ndeg;
    };
    return 0;
}

/****************************************************************************
* mmdnum --- multi minimum degree numbering
* purpose -- this routine performs the final step in producing
*    the permutation and inverse permutation vectors in the
*    multiple elimination version of the minimum degree
*    ordering algorithm.
* input parameters --
*     neqns -- number of equations.
*     qsize -- size of supernodes at elimination.
* updated parameters --
*     invp -- inverse permutation vector. on input,
*             if qsize[node] = 0, then node has been merged
*             into the node -invp[node]; otherwise,
*            -invp[node] is its inverse labelling.
* output parameters --
*     perm -- the permutation vector.
****************************************************************************/
void mmdnum(idx_t neqns, idx_t *perm, idx_t *invp, idx_t *qsize)
{
  idx_t father, nextf, node, nqsize, num, root;

  debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
  debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
  debug("NUMBERING\n");
  debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
  debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
  //PRINT_LIST(perm, neqns);
  //PRINT_LIST(invp, neqns);
  //PRINT_LIST(qsize, neqns);

  for ( node = 1; node <= neqns; node++ ) {
      nqsize = qsize[node];
      if ( nqsize <= 0 ) perm[node] = invp[node];
      if ( nqsize > 0 )  perm[node] = -invp[node];
  };
  // PRINT_LIST(invp, neqns);
  // PRINT_LIST(perm, neqns);

  /* for each node which has been merged, do the following. */
  for ( node = 1; node <= neqns; node++ ) {
      if ( perm[node] <= 0 )  {

	 /* trace the merged tree until one which has not */
         /* been merged, call it root.                    */
         father = node;
         while ( perm[father] <= 0 )
            father = - perm[father];

         /* number node after root. */
         root = father;
         num = perm[root] + 1;
         invp[node] = -num;
         perm[root] = num;

         /* shorten the merged tree. */
         father = node;
         nextf = - perm[father];
         while ( nextf > 0 ) {
            perm[father] = -root;
            father = nextf;
            nextf = -perm[father];
         };
      };  /* end of -- if ( perm[node] <= 0 ) -- */
  }; /* end of -- for ( node = 1; -- */
  debug("449 YOLOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO\n");
  // PRINT_LIST(invp, neqns);
  // PRINT_LIST(perm, neqns);

  /* ready to compute perm. */
  for ( node = 1; node <= neqns; node++ ) {
        num = -invp[node];
        invp[node] = num;
        perm[num] = node;
  };
  return;
}

/****************************************************************************
* mmdupd ---- multiple minimum degree update
* purpose -- this routine updates the degrees of nodes after a
*            multiple elimination step.
* input parameters --
*    ehead -- the beginning of the list of eliminated nodes
*             (i.e., newly formed elements).
*    neqns -- number of equations.
*    (xadj, adjncy) -- adjacency structure.
*    delta -- tolerance value for multiple elimination.
*    maxint -- maximum machine representable (short) integer.
* updated parameters --
*    mdeg -- new minimum degree after degree update.
*    (head, forward, backward) -- degree doubly linked structure.
*    qsize -- size of supernode.
*    list -- marker vector for degree update.
*    *tag   -- tag value.
****************************************************************************/
void mmdupd(idx_t ehead, idx_t neqns, idx_t *xadj, idx_t *adjncy, idx_t delta, idx_t *mdeg,
     idx_t *head, idx_t *forward, idx_t *backward, idx_t *qsize, idx_t *list,
     idx_t *marker, idx_t maxint, idx_t *tag)
{
 idx_t  deg, deg0, element, enode, fnode, i, iq2, istop,
      istart, j, jstop, jstart, link, mdeg0, mtag, nabor,
      node, q2head, qxhead;

      mdeg0 = *mdeg + delta;
      debug("Set mdeg0 to mdeg %ld + delta %ld\n", *mdeg, delta);
      element = ehead;

n100:
      if ( element <= 0 ) return;

      /* for each of the newly formed element, do the following. */
      /* reset tag value if necessary.                           */
      mtag = *tag + mdeg0;
      debug("Set mtag to tag %ld + mdeg0 %ld\n", *tag, mdeg0);
      if ( mtag >= maxint ) {
         *tag = 1;
         for ( i = 1; i <= neqns; i++ )
             if ( marker[i] < maxint ) marker[i] = 0;
         debug("REEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE\n");
         int* x = NULL;
         *x = 5;
         mtag = *tag + mdeg0;
      };

      /* create two linked lists from nodes associated with 'element': */
      /* one with two nabors (q2head) in the adjacency structure, and the*/
      /* other with more than two nabors (qxhead). also compute 'deg0',*/
      /* number of nodes in this element.                              */
      q2head = 0;
      qxhead = 0;
      deg0 = 0;
      link =element;

      debug("Looking at neighbors of element %ld\n", element - 1);
n400:
      istart = xadj[link];
      istop = xadj[link+1] - 1;
      for ( i = istart; i <= istop; i++ ) {
          enode = adjncy[i];
          link = -enode;
          if ( enode < 0 )  goto n400;
          if ( enode == 0 ) {
            // debug("break 538\n");
            break;
          }
          if ( qsize[enode] != 0 ) {
             deg0 += qsize[enode];
             debug("497 Setting marker [%ld] to tag Tag(%ld)\n", enode - 1, mtag);
             marker[enode] = mtag;

             /*'enode' requires a degree update*/
             debug("Checking enode %ld\n", enode - 1);
             if ( backward[enode] == 0 ) {
               debug("Matches\n");
                /* place either in qxhead or q2head list. */
                debug("forward: Next(%ld)\n", forward[enode] - 1);
                if ( forward[enode] != 2 ) {
                    debug("Insert enode %ld in qx\n", enode - 1);
                     list[enode] = qxhead;
                     qxhead = enode;
                } else {
                    debug("Insert enode %ld in q2\n", enode - 1);
                     list[enode] = q2head;
                     q2head = enode;
                };
             };
          }; /* enf of -- if ( qsize[enode] != 0 ) -- */
      }; /* end of -- for ( i = istart; -- */

      /* for each node in q2 list, do the following. */
      debug("ENTER q2\n");
      enode = q2head;
      iq2 = 1;

n900:
      if ( enode <= 0 ) goto n1500;
      if ( backward[enode] != 0 ) goto n2200;
        debug("enode %ld in q2\n", enode - 1);
      (*tag)++;
      deg = deg0;

      /* identify the other adjacent element nabor. */
      istart = xadj[enode];
      nabor = adjncy[istart];
      if ( nabor == element ) nabor = adjncy[istart+1];
      link = nabor;
      if ( forward[nabor] >= 0 ) {
           /* nabor is uneliminated, increase degree count. */
           deg += qsize[nabor];
           goto n2100;
      };

       /* the nabor is eliminated. for each node in the 2nd element */
       /* do the following.                                         */
n1000:
       istart = xadj[link];
       istop = xadj[link+1] - 1;
       for ( i = istart; i <= istop; i++ ) {
           node = adjncy[i];
           link = -node;
           if ( node != enode ) {
                if ( node < 0 ) goto n1000;
                if ( node == 0 )  goto n2100;
                if ( qsize[node] != 0 ) {
                     if ( marker[node] < *tag ) {
                        /* 'node' is not yet considered. */
                        debug("549 Setting marker [%ld] to tag Tag(%ld)\n", node - 1, *tag);
                        marker[node] = *tag;
                        deg += qsize[node];
                     } else {
                        if ( backward[node] == 0 ) {
                             if ( forward[node] == 2 ) {
                                /* 'node' is indistinguishable from 'enode'.*/
                                /* merge them into a new supernode.         */
                                qsize[enode] += qsize[node];
                                qsize[node] = 0;
                                debug("559 Setting marker [%ld] to Maxint\n", node - 1);
                                marker[node] = maxint;
                                forward[node] = -enode;
                                backward[node] = -maxint;
                             } else {
                                /* 'node' is outmacthed by 'enode' */
				if (backward[node]==0) backward[node] = -maxint;
                             };
                        }; /* end of -- if ( backward[node] == 0 ) -- */
                    }; /* end of -- if ( marker[node] < *tag ) -- */
                }; /* end of -- if ( qsize[node] != 0 ) -- */
              }; /* end of -- if ( node != enode ) -- */
          }; /* end of -- for ( i = istart; -- */
          goto n2100;

n1500:
          /* for each 'enode' in the 'qx' list, do the following. */
          debug("ENTER qx\n");
          enode = qxhead;
          iq2 = 0;

n1600:    if ( enode <= 0 ) {
            // debug("break 631, enode %ld\n", enode - 1);
            goto n2300;
          }
          debug("enode %ld in qx\n", enode - 1);
          if ( backward[enode] != 0 ) {
            if (backward[enode] == -maxint) {
              debug("continue 635, backward: NegMaxInt\n");
            } else {
              debug("continue 635, backward: %ld\n", backward[enode]);
            }
            goto n2200;
          }
          (*tag)++;
          deg = deg0;

          /*for each unmarked nabor of 'enode', do the following.*/
          istart = xadj[enode];
          istop = xadj[enode+1] - 1;
          for ( i = istart; i <= istop; i++ ) {
                nabor = adjncy[i];
                if ( nabor == 0 ) break;
                if ( marker[nabor] < *tag ) {
                     debug("591 Setting marker [%ld] to tag Tag(%ld)\n", nabor - 1, *tag);
                     marker[nabor] = *tag;
                     link = nabor;
                     if ( forward[nabor] >= 0 ) 
                          /*if uneliminated, include it in deg count.*/
                          deg += qsize[nabor];
                     else {
n1700:
                          /* if eliminated, include unmarked nodes in this*/
                          /* element into the degree count.             */
                          jstart = xadj[link];
                          jstop = xadj[link+1] - 1;
                          for ( j = jstart; j <= jstop; j++ ) {
                                node = adjncy[j];
                                link = -node;
                                if ( node < 0 ) goto n1700;
                                if ( node == 0 ) break;
                                if ( marker[node] < *tag ) {
                                    debug("609 Setting marker [%ld] to tag Tag(%ld)\n", node - 1, *tag);
                                    marker[node] = *tag;
                                    deg += qsize[node];
                                };
                          }; /* end of -- for ( j = jstart; -- */
                     }; /* end of -- if ( forward[nabor] >= 0 ) -- */
                  }; /* end of -- if ( marker[nabor] < *tag ) -- */
          }; /* end of -- for ( i = istart; -- */

n2100:
          /* update external degree of 'enode' in degree structure, */
          /* and '*mdeg' if necessary.                     */
          deg = deg - qsize[enode] + 1;
          fnode = head[deg];
          forward[enode] = fnode;
          debug("639 Set backward %ld to Degree(%ld)\n", enode - 1, deg - 1);
          backward[enode] = -deg;
          if ( fnode > 0 ) { debug("642 Set backward %ld to Previous(%ld)\n", fnode - 1, enode - 1); backward[fnode] = enode; }
              if (enode == 0) {
                debug("640 Set head %ld to None\n", deg - 1);
              } else if (enode > 0) {
                debug("640 Set head %ld to Next(%ld)\n", deg - 1, enode - 1);
              } else {
                debug("640 Set head %ld to NextNeg(%ld)\n", deg - 1, -enode - 1);
              }
          head[deg] = enode;
          if ( deg < *mdeg ) *mdeg = deg;

n2200:
          /* get next enode in current element. */
          enode = list[enode];
          if ( iq2 == 1 ) goto n900;
          goto n1600;

n2300:
          /* get next element in the list. */
          *tag = mtag;
          element = list[element];
          goto n100;
    }
