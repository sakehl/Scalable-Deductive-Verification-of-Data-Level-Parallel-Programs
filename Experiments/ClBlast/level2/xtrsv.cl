#include "level2.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains kernels to perform forward or backward substition, as used in the TRSV routine
//
// =================================================================================================

// Enables loading of this file using the C++ pre-processor's #include (C++11 standard raw string
// literal). Comment-out this line for syntax-highlighting when developing.
//R"(

// =================================================================================================
// #if defined(ROUTINE_TRSV)

// __kernel
// void FillVector(const int n, const int inc, const int offset,
//                 __global real* restrict dest, const real_arg arg_value) {
//   const real value = GetRealArg(arg_value);
//   const int tid = get_global_id(0);
//   if (tid < n) {
//     dest[tid*inc + offset] = value;
//   }
// }

// =================================================================================================

// Parameters set by the tuner or by the database. Here they are given a basic default value in case
// this kernel file is used outside of the CLBlast library.

#ifndef TRSV_BLOCK_SIZE
  // The block size for forward or backward substition
#define TRSV_BLOCK_SIZE 32    
  //@ inline pure int TRSV_BLOCK_SIZE() = 32;
#endif

/*@



  requires 0 <= i && i<|b|;
  requires |x| == |b| && |l| == |b| && (\forall int j; 0 <= j && j < |b|; |{:l[j]:}| == |b|);
pure float xsol(seq<float> b, seq<seq<float> > l, seq<float> x, int i, bool transposed) = 
  (b[i] - x[i] - xsolh(b, l, x, i, i, transposed))/l[i][i];



  requires 0 <= i && i<|b|;
  requires 0 <= j && j<=i;
  requires |x| == |b| && |l| == |b| && (\forall int j; 0 <= j && j <|b|; |{:l[j]:}| == |b|);
pure float xsolh(seq<float> b, seq<seq<float> > l, seq<float> x, int i, int j, bool transposed) = 
  (j==0) ? 0 :
  (\let float _l = transposed ? l[j-1][i] : l[i][j-1];
  _l * xsol(b, l, x, j-1, transposed) + xsolh(b, l, x, i, j-1, transposed)
  );


@*/

// =================================================================================================

#ifdef EXTRACT_BODY
/*@ extract_body */
#endif
/*@
  given seq<float> _x;
  given seq<float> _b;
  given seq<seq<float > > _A;

  context get_num_groups(0) == 1 && get_num_groups(1) == 1 && get_num_groups(2) == 1;
  context get_local_size(0) == TRSV_BLOCK_SIZE() && get_local_size(1) == 1 && get_local_size(2) == 1;
  context n >= 1 && n <= TRSV_BLOCK_SIZE();
  context x_inc >= 1 && x_offset >= 0;
  context b_inc >= 1 && b_offset >= 0;
  context x != NULL && \pointer_length(x) >= n*x_inc+x_offset;
  context b != NULL && \pointer_length(b) >= n*b_inc+b_offset;
  context A != NULL && a_offset >= 0;
  context a_ld >= n && \pointer_length(A) >= a_ld * n + a_offset;
  
  context \ltid < n ==> Perm({:x[acc1d(\ltid, x_offset, n, x_inc)]:}, write);*/
#ifndef CONST_TYPES
/*@ context (\forall* int i; 0 <=i && i<\pointer_length(A); Perm({:A[i]:}, read));
    context \ltid < n ==> Perm({:b[acc1d(\ltid, b_offset, n, b_inc)]:}, read);*/
#endif
  /*@context |_x| == n;
  context \ltid < n ==> \old(x[acc1d(\ltid, x_offset, n, x_inc)]) == {:_x[\ltid]:};
  context |_b| == n;
  context \ltid < n ==> (b[acc1d(\ltid, b_offset, n, b_inc)]) == {:_b[\ltid]:};
  context |_A| == n && (\forall int i; 0 <= i && i<n; |{:_A[i]:}| == n);
  context (\forall int i, int j; 0 <= i && i<n && 0 <= j && j<n;
    A[acc2d(j, i, a_offset, a_ld, n, a_ld)] == {:_A[j][i]:});
  context is_unit_diagonal != 0 ==> (\forall int i; 0 <= i && i<n; {:_A[i][i]:} == 1);

  context (\forall* int i; 0 <= i && i<TRSV_BLOCK_SIZE(); Perm({:alm[i][\ltid]:}, write));
  context Perm({:xlm[\ltid]:}, write);
  ensures \ltid < n ==> {:x[acc1d(\ltid, x_offset, n, x_inc)]:} == xsol(_b, _A, _x, \ltid, is_transposed!=0); */
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(TRSV_BLOCK_SIZE, 1, 1)))
#endif
void trsv_forward(int n,
                  READ_ONLY1 __global real *A, const int a_offset, int a_ld,
                  READ_ONLY2 __global real *b, const int b_offset, int b_inc,
                  UNIQUE3 __global real *x, const int x_offset, int x_inc,          
                  const int is_transposed, const int is_unit_diagonal, const int do_conjugate) {
  UNIQUE4 __local real alm[TRSV_BLOCK_SIZE][TRSV_BLOCK_SIZE];
  UNIQUE5 __local real xlm[TRSV_BLOCK_SIZE];
  const int tid = get_local_id(0);
  

  // Pre-loads the data into local memory
  if (tid < n) {
    int bid = tid*b_inc + b_offset;
    int xid = tid*x_inc + x_offset;
    //@ assert bid == acc1d(tid, b_offset, n, b_inc);
    //@ assert xid == acc1d(tid, x_offset, n, x_inc);
    Subtract(xlm[tid], b[bid], x[xid]);
    if (is_transposed == 0) {
      #ifndef CONST_TYPES
      /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(A); Perm({:A[i]:}, read)); 
          loop_invariant (\forall int i, int j; 0 <= i && i<n && 0 <= j && j<n;
    \old(A[acc2d(j, i, a_offset, a_ld, n, a_ld)]) == {:A[acc2d(j, i, a_offset, a_ld, n, a_ld)]:}); */
      #endif
      /*@ loop_invariant 0 <= i && i <= n;
        loop_invariant (\forall* int j; 0 <= j && j<n; Perm({:alm[j][\ltid]:}, write));
        loop_invariant (\forall int i, int j; 0 <= i && i<n && 0 <= j && j<n;
          \old(A[acc2d(j, i, a_offset, a_ld, n, a_ld)]) == {:_A[j][i]:});
        loop_invariant (\forall* int j; 0 <= j && j<i; {:alm[j][\ltid]:} == _A[j][\ltid]);
      */
      for (int i = 0; i < n; ++i) {
        int id = i + tid*a_ld + a_offset;
        //@ assert id == acc2d(i, tid, a_offset, a_ld, n, a_ld);
        alm[i][tid] = A[id];
      }
    }
    else {
      #ifndef CONST_TYPES
      /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(A); Perm({:A[i]:}, read)); 
          loop_invariant (\forall int i, int j; 0 <= i && i<n && 0 <= j && j<n;
    \old(A[acc2d(j, i, a_offset, a_ld, n, a_ld)]) == {:A[acc2d(j, i, a_offset, a_ld, n, a_ld)]:}); */
      #endif
      /*@ loop_invariant 0 <= i && i <= n;
        loop_invariant (\forall* int j; 0 <= j && j<n; Perm({:alm[j][\ltid]:}, write));
        loop_invariant (\forall int i, int j; 0 <= i && i<n && 0 <= j && j<n;
          \old(A[acc2d(j, i, a_offset, a_ld, n, a_ld)]) == {:_A[j][i]:});
        loop_invariant (\forall* int j; 0 <= j && j<i; {:alm[j][\ltid]:} == _A[\ltid][j]);*/
      for (int i = 0; i < n; ++i) {
        int id = tid + i*a_ld + a_offset;
        //@ assert id == acc2d(tid, i, a_offset, a_ld, n, a_ld);
        alm[i][tid] = A[id];
      }
    }
    if (do_conjugate != 0) {
      /*@ loop_invariant 0 <= i && i <= n;
        loop_invariant (\forall* int j; 0 <= j && j<n; Perm({:alm[j][\ltid]:}, write));
        loop_invariant (\forall* int j; i <= j && j<n; {:alm[j][\ltid]:} == (is_transposed!=0 ?_A[\ltid][j] : _A[j][\ltid]));
        // Change for complex numbers
        loop_invariant (\forall* int j; 0 <= j && j<i; {:alm[j][\ltid]:} == (is_transposed!=0 ?_A[\ltid][j] : _A[j][\ltid]));*/
      for (int i = 0; i < n; ++i) {
        COMPLEX_CONJUGATE(alm[i][tid]);
      }
    }
  }
  
  /*@ requires (\forall* int j; \ltid<n && 0 <= j && j<n; Perm({:alm[j][\ltid]:}, 1\2));
  requires (\forall int j; \ltid<n && 0 <= j && j<n; {:alm[j][\ltid]:} == (is_transposed!=0 ?_A[\ltid][j] : _A[j][\ltid]));
  ensures (\forall* int i, int j; \ltid==0 && 0 <= i && i<n && 0 <= j && j<n; Perm({:alm[j][i]:}, 1\2));
  ensures (\forall int i, int j; \ltid==0 && 0 <= i && i<n && 0 <= j && j<n; {:alm[j][i]:}== (is_transposed!=0 ?_A[i][j] : _A[j][i]));

  requires \ltid<n ==> Perm({:xlm[\ltid]:}, write);
  requires \ltid<n ==> {:xlm[\ltid]:} == _b[\ltid] - _x[\ltid];
  ensures (\forall* int j; \ltid==0 && 0 <= j && j<n;  Perm({:xlm[j]:}, write));
  ensures (\forall int j; \ltid==0 && 0 <= j && j<n; {:xlm[j]:} == _b[j] - _x[j]);*/
  barrier(CLK_LOCAL_MEM_FENCE);

  // Computes the result (single-threaded for now)
  if (tid == 0) {
    //@ extract
    /*@ loop_invariant 0 <= i && i <= n;
      loop_invariant n <= TRSV_BLOCK_SIZE();
      loop_invariant |_b| == n && |_x| == n && |_A| == n && (\forall int i; 0 <= i && i<n; |{:_A[i]:}| == n);
      loop_invariant (\forall* int j; 0 <= j && j<n; Perm({:xlm[j]:}, write));
      loop_invariant (\forall* int j, int k; 0 <= j && j<n && 0 <= k && k<n; Perm({:alm[j][k]:}, 1\2));
      loop_invariant (\forall int i, int j; 0 <= i && i<n && 0 <= j && j<n; 
        {:alm[j][i]:}== (is_transposed!=0 ?_A[i][j] : _A[j][i]));
      loop_invariant is_unit_diagonal != 0 ==> (\forall int i; 0 <= i && i<n; {:_A[i][i]:} == 1);
      loop_invariant (\forall int j; i <= j && j<n; {:xlm[j]:} == _b[j] - _x[j]);
      loop_invariant (\forall int j; 0 <= j && j<i && j<n; {:xlm[j]:} == xsol(_b, _A, _x, j, is_transposed!=0));*/
    for (int i = 0; i < n; ++i) {
      /*@ loop_invariant 0 <= j && j <= i && 0 <= i && i < n;
        loop_invariant Perm(xlm[i], write);
        loop_invariant (\forall* int k; 0 <= k && k<i; Perm({:xlm[k]:}, 1\2));
        loop_invariant (\forall int k; 0 <= k && k<i && k<n; {:xlm[k]:} == xsol(_b, _A, _x, k, is_transposed!=0));
        loop_invariant (\forall* int j, int k; 0 <= j && j<n && 0 <= k && k<n; Perm({:alm[j][k]:}, 1\2));
        loop_invariant (\forall int i, int j; 0 <= i && i<n && 0 <= j && j<n; 
          {:alm[j][i]:}== (is_transposed!=0 ?_A[i][j] : _A[j][i]));
        loop_invariant {:xlm[i]:} == _b[i] - _x[i] - xsolh(_b, _A, _x, i, j, is_transposed!=0);*/
      for (int j = 0; j < i; ++j) {
        MultiplySubtract(xlm[i], alm[i][j], xlm[j]);
      }
      if (is_unit_diagonal == 0) { 
        DivideFull(xlm[i], xlm[i], alm[i][i]); 
      }
    }
  }

  /*@ requires (\forall* int i, int j; \ltid==0 && 0 <= i && i<n && 0 <= j && j<n; Perm({:alm[i][j]:}, 1\2));
    ensures (\forall* int i; \ltid<n && 0 <= i && i<n; Perm({:alm[i][\ltid]:}, 1\2));
    requires (\forall* int j; \ltid==0 && 0 <= j && j<n;  Perm({:xlm[j]:}, write));
    requires (\forall int j; \ltid==0 && 0 <= j && j<n; {:xlm[j]:} == xsol(_b, _A, _x, j, is_transposed!=0));
    ensures \ltid<n ==> Perm({:xlm[\ltid]:}, write);
    ensures \ltid<n ==> {:xlm[\ltid]:} == xsol(_b, _A, _x, \ltid, is_transposed!=0);*/
  barrier(CLK_LOCAL_MEM_FENCE);

  // Stores the results
  if (tid < n) {
    int xid = tid*x_inc + x_offset;
    //@ assert xid == acc1d(tid, x_offset, n, x_inc);
    x[xid] = xlm[tid];
  }
}
#ifdef COMMENT_OUT
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel __attribute__((reqd_work_group_size(TRSV_BLOCK_SIZE, 1, 1)))
#endif
void trsv_backward(int n,
                   const __global real *A, const int a_offset, int a_ld,
                   __global real *b, const int b_offset, int b_inc,
                   __global real *x, const int x_offset, int x_inc,
                   const int is_transposed, const int is_unit_diagonal, const int do_conjugate) {
  __local real alm[TRSV_BLOCK_SIZE][TRSV_BLOCK_SIZE];
  __local real xlm[TRSV_BLOCK_SIZE];
  const int tid = get_local_id(0);

  // Pre-loads the data into local memory
  if (tid < n) {
    Subtract(xlm[tid], b[tid*b_inc + b_offset], x[tid*x_inc + x_offset]);
    if (is_transposed == 0) {
      for (int i = 0; i < n; ++i) {
        alm[i][tid] = A[i + tid*a_ld + a_offset];
      }
    }
    else {
      for (int i = 0; i < n; ++i) {
        alm[i][tid] = A[tid + i*a_ld + a_offset];
      }
    }
    if (do_conjugate != 0) {
      for (int i = 0; i < n; ++i) {
        COMPLEX_CONJUGATE(alm[i][tid]);
      }
    }
  }
  barrier(CLK_LOCAL_MEM_FENCE);

  // Computes the result (single-threaded for now)
  if (tid == 0) {
    for (int i = n - 1; i >= 0; --i) {
      for (int j = i + 1; j < n; ++j) {
        MultiplySubtract(xlm[i], alm[i][j], xlm[j]);
      }
      if (is_unit_diagonal == 0) { DivideFull(xlm[i], xlm[i], alm[i][i]); }
    }
  }
  barrier(CLK_LOCAL_MEM_FENCE);

  // Stores the results
  if (tid < n) {
    x[tid*x_inc + x_offset] = xlm[tid];
  }
}

#endif
// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
