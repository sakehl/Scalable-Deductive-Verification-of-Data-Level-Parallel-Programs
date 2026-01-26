#include "level1.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains the Xamax kernel. It implements index of (absolute) min/max computation using
// reduction kernels. Reduction is split in two parts. In the first (main) kernel the X vector is
// loaded, followed by a per-thread and a per-workgroup reduction. The second (epilogue) kernel
// is executed with a single workgroup only, computing the final result.
//
// =================================================================================================

// Enables loading of this file using the C++ pre-processor's #include (C++11 standard raw string
// literal). Comment-out this line for syntax-highlighting when developing.
//R"(

// Parameters set by the tuner or by the database. Here they are given a basic default value in case
// this kernel file is used outside of the CLBlast library.
#ifndef WGS1
  // The local work-group size of the main kernel
#define WGS1 64
  //@ inline pure int WGS1() = 64;
#endif
#ifndef WGS2
  // The local work-group size of the epilogue kernel
#define WGS2 64     
  //@ inline pure int WGS2() = 64;
#endif

// =================================================================================================

#ifdef EXTRACT_BODY
/*@ extract_body */
#endif
/*@ context get_num_groups(1) == 1 && get_num_groups(2) == 1;
  context get_local_size(0) == WGS1() && get_local_size(1) == 1 && get_local_size(2) == 1;
  context n >= 1 && x_inc >= 1 && x_offset >= 0;
  context xgm != NULL && \pointer_length(xgm) >= n*x_inc+x_offset;
  context maxgm != NULL && \pointer_length(maxgm) >= get_num_groups(0);
  context \ltid==0 ==> Perm({:maxgm[get_group_id(0)]:}, write);
  context imaxgm != NULL && \pointer_length(imaxgm) >= get_num_groups(0);
  context \ltid==0 ==> Perm({:imaxgm[get_group_id(0)]:}, write);
  requires Perm({:maxlm[\ltid]:}, write);
  requires Perm({:imaxlm[\ltid]:}, write); @*/
#ifndef CONST_TYPES
//@ context (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
#endif
// The main reduction kernel, performing the loading and the majority of the operation
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(WGS1, 1, 1)))
#endif
void Xamax(const int n,
           READ_ONLY1 __global real* restrict xgm, const int x_offset, const int x_inc,
           UNIQUE2 __global singlereal* maxgm, UNIQUE2 __global unsigned int* imaxgm) {
  UNIQUE3 __local singlereal maxlm[WGS1];
  UNIQUE3 __local unsigned int imaxlm[WGS1];
  const int lid = get_local_id(0);
  const int wgid = get_group_id(0);
  const int num_groups = get_num_groups(0);

  // Performs loading and the first steps of the reduction
  #if defined(ROUTINE_MAX) || defined(ROUTINE_MIN) || defined(ROUTINE_AMIN)
    singlereal max = SMALLEST;
  #else
    singlereal max = ZERO;
  #endif
  unsigned int imax = 0;
  int id = wgid*WGS1 + lid;
  /*@
    loop_invariant 0 <= id && id <= n + WGS1() * num_groups;
    loop_invariant id % (WGS1() * num_groups) == wgid * WGS1() + lid;
  @*/
#ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
#endif
  while (id < n) {
    const int x_index = id*x_inc + x_offset;
    #if PRECISION == 3232 || PRECISION == 6464
      singlereal x = fabs(xgm[x_index].x) + fabs(xgm[x_index].y);
    #else
      singlereal x = xgm[x_index];
    #endif
    #if defined(ROUTINE_MAX) // non-absolute maximum version
      // nothing special here
    #elif defined(ROUTINE_MIN) // non-absolute minimum version
      x = -x;
    #elif defined(ROUTINE_AMIN) // absolute minimum version
      x = -fabs(x);
    #else
      x = fabs(x);
    #endif
    if (x > max) {
      max = x;
      imax = id;
    }
    //@ assert lemma_mod(id, WGS1() * num_groups);
    id += WGS1*num_groups;
  }
  maxlm[lid] = max;
  imaxlm[lid] = imax;
  /*@ requires \ltid >= WGS1()/2 ==> Perm({:maxlm[\ltid]:}, write);
    requires \ltid >= WGS1()/2 ==> Perm({:imaxlm[\ltid]:}, write);
    ensures  \ltid <  WGS1()/2 ==> Perm({:maxlm[\ltid+WGS1()/2]:}, write);
    ensures  \ltid <  WGS1()/2 ==> Perm({:imaxlm[\ltid+WGS1()/2]:}, write); @*/
  barrier(CLK_LOCAL_MEM_FENCE);

  //@ ghost int t = 2;
  /*@ loop_invariant  s >= 0 && s <= WGS1()/2;
    loop_invariant s>0 ==> t >= 2 && t <= WGS1();
    loop_invariant s>0 ==> s*t == WGS1();
    loop_invariant \ltid < s ==> Perm({:maxlm[\ltid]:}, write) ** Perm({:maxlm[\ltid+s]:}, write);
    loop_invariant s==0 && \ltid==0 ==> Perm({:maxlm[\ltid]:}, write);
    loop_invariant \ltid < s ==> Perm({:imaxlm[\ltid]:}, write) ** Perm({:imaxlm[\ltid+s]:}, write);
    loop_invariant s==0 && \ltid==0 ==> Perm({:imaxlm[\ltid]:}, write); @*/
  // Performs reduction in local memory
  for (int s=WGS1/2; s>0; s=s>>1) {
    if (lid < s) {
      if (maxlm[lid + s] > maxlm[lid]) {
        maxlm[lid] = maxlm[lid + s];
        imaxlm[lid] = imaxlm[lid + s];
      }
    }
    /*@ requires \ltid >= s/2 && \ltid<s ==> Perm({:maxlm[\ltid]:}, write);
      ensures  \ltid <  s/2 ==> Perm({:maxlm[\ltid+s/2]:}, write);
      ensures s/2==0 && \ltid==0 ==> Perm({:maxlm[\ltid]:}, write);
      requires \ltid >= s/2 && \ltid<s ==> Perm({:imaxlm[\ltid]:}, write);
      ensures  \ltid <  s/2 ==> Perm({:imaxlm[\ltid+s/2]:}, write);
      ensures s/2==0 && \ltid==0 ==> Perm({:imaxlm[\ltid]:}, write);
    @*/
    barrier(CLK_LOCAL_MEM_FENCE);
    //@ ghost t *= 2;
  }

  // Stores the per-workgroup result
  if (lid == 0) {
    maxgm[wgid] = maxlm[0];
    imaxgm[wgid] = imaxlm[0];
  }
}

// =================================================================================================
#ifdef NOT_IGNORE
// The epilogue reduction kernel, performing the final bit of the operation. This kernel has to
// be launched with a single workgroup only.
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel __attribute__((reqd_work_group_size(WGS2, 1, 1)))
#endif
void XamaxEpilogue(const __global singlereal* restrict maxgm,
                   const __global unsigned int* restrict imaxgm,
                   __global unsigned int* imax, const int imax_offset) {
  __local singlereal maxlm[WGS2];
  __local unsigned int imaxlm[WGS2];
  const int lid = get_local_id(0);

  // Performs the first step of the reduction while loading the data
  if (maxgm[lid + WGS2] > maxgm[lid]) {
    maxlm[lid] = maxgm[lid + WGS2];
    imaxlm[lid] = imaxgm[lid + WGS2];
  }
  else {
    maxlm[lid] = maxgm[lid];
    imaxlm[lid] = imaxgm[lid];
  }
  barrier(CLK_LOCAL_MEM_FENCE);

  // Performs reduction in local memory
  for (int s=WGS2/2; s>0; s=s>>1) {
    if (lid < s) {
      if (maxlm[lid + s] > maxlm[lid]) {
        maxlm[lid] = maxlm[lid + s];
        imaxlm[lid] = imaxlm[lid + s];
      }
    }
    barrier(CLK_LOCAL_MEM_FENCE);
  }

  // Stores the final result
  if (lid == 0) {
    imax[imax_offset] = imaxlm[0];
  }
}
#endif

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
