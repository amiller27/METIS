/*
 * Copyright 1997, Regents of the University of Minnesota
 *
 * metis.h
 *
 * This file includes all necessary header files
 *
 * Started 8/27/94
 * George
 *
 * $Id: metislib.h 10655 2011-08-02 17:38:11Z benjamin $
 */

#ifndef _LIBMETIS_METISLIB_H_
#define _LIBMETIS_METISLIB_H_

#include <GKlib.h>

#if defined(ENABLE_OPENMP)
  #include <omp.h>
#endif


#include <metis.h>
#include "rename.h"
#include "gklib_defs.h"

#include "defs.h"
#include "struct.h"
#include "macros.h"
#include "proto.h"


#if defined(COMPILER_MSC)
#if defined(rint)
  #undef rint
#endif
#define rint(x) ((idx_t)((x)+0.5))  /* MSC does not have rint() function */
#endif

#define DEBUG_COARSEN 0
#define DEBUG_COMPRESS 0
#define DEBUG_FM 0
#define DEBUG_INITPART 0
#define DEBUG_MMD 0
#define DEBUG_OMETIS 1
#define DEBUG_SEPARATOR 0
#define DEBUG_TWO_SIDED 0
#define DEBUG_ONE_SIDED 0
#define DEBUG_BALANCE 0
#define DEBUG_SEPARATOR_REFINEMENT 0

#endif
