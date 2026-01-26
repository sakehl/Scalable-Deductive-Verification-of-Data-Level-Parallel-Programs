#include "level1.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains the Xdot kernel. It implements a dot-product computation using reduction
// kernels. Reduction is split in two parts. In the first (main) kernel the X and Y vectors are
// multiplied, followed by a per-thread and a per-workgroup reduction. The second (epilogue) kernel
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

// The main reduction kernel, performing the multiplication and the majority of the sum operation
#ifdef EXTRACT_BODY
/*@ extract_body */
#endif
#ifndef CONST_TYPES
//@ context xgm!=NULL ** (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
//@ context ygm!=NULL ** (\forall* int i; 0 <=i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));
#endif
/*@ context get_num_groups(1) == 1 && get_num_groups(2) == 1;
  context get_local_size(0) == WGS1() && get_local_size(1) == 1 && get_local_size(2) == 1;
  context n >= 1 && x_inc >= 1 && x_offset >= 0
    && y_inc >= 1 && y_offset >= 0;
  context xgm != NULL && \pointer_length(xgm) >= n*x_inc+x_offset;
  context ygm != NULL && \pointer_length(ygm) >= n*y_inc+y_offset;
  context output != NULL && \pointer_length(output) >= get_num_groups(0);
  context \ltid==0 ==> Perm({:output[get_group_id(0)]:}, write);
  requires Perm({:lm[\ltid]:}, write); @*/
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(WGS1, 1, 1)))
#endif
void Xdot(const int n,
          READ_ONLY1 __global real* restrict xgm, const int x_offset, const int x_inc,
          READ_ONLY2 __global real* restrict ygm, const int y_offset, const int y_inc,
          UNIQUE3 __global real* output, const bool do_conjugate
  ) {
  UNIQUE4 __local real lm[WGS1];
  const int lid = get_local_id(0);
  const int wgid = get_group_id(0);
  const int num_groups = get_num_groups(0);

  // Performs multiplication and the first steps of the reduction
  real acc;
  SetToZero(acc);
  int id = wgid*WGS1 + lid;
#ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
  //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));
#endif
  /*@
    loop_invariant 0 <= id && id <= n + WGS1() * num_groups;
    loop_invariant id % (WGS1() * num_groups) == wgid * WGS1() + lid;
  @*/
  while (id < n) {
    int idx = id*x_inc + x_offset;
    int idy = id*y_inc + y_offset;
    /*@
      assert acc1d(id, x_offset, n, x_inc) == idx;
      assert acc1d(id, y_offset, n, y_inc) == idy;
    @*/
    real x = xgm[idx];
    real y = ygm[idy];
    if (do_conjugate) { COMPLEX_CONJUGATE(x); }
    MultiplyAdd(acc, x, y);
    //@ assert lemma_mod(id, WGS1() * num_groups);
    id += WGS1*num_groups;
  }
  lm[lid] = acc;
  /*@ 
    requires \ltid >= WGS1()/2 ==> Perm({:lm[\ltid]:}, write);
    ensures  \ltid <  WGS1()/2 ==> Perm({:lm[\ltid+WGS1()/2]:}, write);
  @*/
  barrier(CLK_LOCAL_MEM_FENCE);

  // Performs reduction in local memory
  //@ ghost int t = 2;
  /*@
    loop_invariant  s >= 0 && s <= WGS1()/2;
    loop_invariant s>0 ==> t >= 2 && t <= WGS1();
    loop_invariant s>0 ==> s*t == WGS1();
    loop_invariant \ltid < s ==> Perm({:lm[\ltid]:}, write) ** Perm({:lm[\ltid+s]:}, write);
    loop_invariant s==0 && \ltid==0 ==> Perm({:lm[\ltid]:}, write);
  @*/
  for (int s=WGS1/2; s>0; s=s>>1) {
    if (lid < s) {
      Add(lm[lid], lm[lid], lm[lid + s]);
    }
    /*@ 
      requires \ltid >= s/2 && \ltid<s ==> Perm({:lm[\ltid]:}, write);
      ensures  \ltid <  s/2 ==> Perm({:lm[\ltid+s/2]:}, write);
      ensures s/2==0 && \ltid==0 ==> Perm({:lm[\ltid]:}, write);
    @*/
    barrier(CLK_LOCAL_MEM_FENCE);
    /*@
      ghost t *= 2;
    @*/
  }

  // Stores the per-workgroup result
  if (lid == 0) {
    output[wgid] = lm[0];
  }
}

// =================================================================================================
#ifdef NOT_IGNORE
The epilogue reduction kernel, performing the final bit of the sum operation. This kernel has to
be launched with a single workgroup only.
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel __attribute__((reqd_work_group_size(WGS2, 1, 1)))
#endif
void XdotEpilogue(const __global real* restrict input,
                  __global real* dot, const int dot_offset) {
  __local real lm[WGS2];
  const int lid = get_local_id(0);

  // Performs the first step of the reduction while loading the data
  Add(lm[lid], input[lid], input[lid + WGS2]);
  barrier(CLK_LOCAL_MEM_FENCE);

  // Performs reduction in local memory
  for (int s=WGS2/2; s>0; s=s>>1) {
    if (lid < s) {
      Add(lm[lid], lm[lid], lm[lid + s]);
    }
    barrier(CLK_LOCAL_MEM_FENCE);
  }

  // Stores the final result
  if (lid == 0) {
    dot[dot_offset] = lm[0];
  }
}
#endif

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
