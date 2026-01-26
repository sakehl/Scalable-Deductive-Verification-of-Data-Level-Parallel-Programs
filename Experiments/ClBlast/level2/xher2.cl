#include "level2.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains the Xher2 kernels for rank-2 matrix update.
//
// =================================================================================================
// #define NO_FRAME
// Enables loading of this file using the C++ pre-processor's #include (C++11 standard raw string
// literal). Comment-out this line for syntax-highlighting when developing.
//R"(
#ifndef WGS1
  // The local work-group size in first dimension
#define WGS1 8    
  //@ inline pure int WGS1() = 8;
#endif
// =================================================================================================

#ifdef EXTRACT_BODY
/*@ extract_body */
#endif
/*@ context get_num_groups(0) == 10 && get_num_groups(1) == 4 && get_num_groups(2) == 1;
  context get_local_size(0) == WGS1() && get_local_size(1) == WGS2() && get_local_size(2) == 1;
  context n >= 1;
  context x_inc >= 1 && x_offset >= 0 && xgm != NULL && \pointer_length(xgm) >= n*x_inc+x_offset;
  context y_inc >= 1 && y_offset >= 0 && ygm != NULL && \pointer_length(ygm) >= n*y_inc+y_offset;
  context agm != NULL && a_offset >= 0;
  context is_rowmajor == 0 || is_rowmajor == 1;
  context a_ld >= n && \pointer_length(agm) >= a_ld * n + a_offset;
  context (\forall* int i, int j; 0 <= i && i < WPT() &&  0 <= j && j < WPT() &&
    i*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
    Perm({:agm[acc2d(i*get_global_size(0) + get_global_id(0), 
                   j*get_global_size(1) + get_global_id(1),
                   a_offset, a_ld, n, a_ld)]:}, write));*/
#ifndef CONST_TYPES
/*@ context (\forall* int i; 0 <=i && i<n; Perm({:xgm[acc1d(i, x_offset, n, x_inc)]:}, read));
    context (\forall* int i; 0 <=i && i<n; Perm({:ygm[acc1d(i, y_offset, n, y_inc)]:}, read)); */
#endif
/*@ ensures (\forall* int i, int j; 0 <= i && i < WPT() && 0 <= j && j < WPT() &&
      i*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
      (\let int id1 = i*get_global_size(0) + get_global_id(0);
      (\let int id2 = j*get_global_size(1) + get_global_id(1);
        !((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) && id1>=0 && id2>=0 ==>
        {:agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]:} ==
          \old(agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]) + arg_alpha * 
          LoadVector(id2, n, xgm, x_offset, x_inc, 1-is_rowmajor) *
          LoadVector(id1, n, ygm, y_offset, y_inc, is_rowmajor) + arg_alpha *
          LoadVector(id1, n, xgm, x_offset, x_inc, is_rowmajor) *
          LoadVector(id2, n, ygm, y_offset, y_inc, 1-is_rowmajor))));*/
// Symmetric version of the rank-2 matrix update kernel (HER2, HPR2, SYR2, SPR2)
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(WGS1, WGS2, 1)))
#endif
void Xher2(const int n,
           const real_arg arg_alpha,
           READ_ONLY1 __global real* restrict xgm, const int x_offset, const int x_inc,
           READ_ONLY2 __global real* restrict ygm, const int y_offset, const int y_inc,
           UNIQUE3 __global real* restrict agm, const int a_offset, const int a_ld,
           const int is_upper, const int is_rowmajor) {
  const real alpha = GetRealArg(arg_alpha);

  // Register storage for X and Y
  //#pragma promote_to_registers
  UNIQUE4 real xvalues[WPT];
  //#pragma promote_to_registers
  UNIQUE5 real yvalues[WPT];
  //#pragma promote_to_registers
  UNIQUE6 real xtvalues[WPT];
  //#pragma promote_to_registers
  UNIQUE7 real ytvalues[WPT];

  #ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<n; Perm({:xgm[acc1d(i, x_offset, n, x_inc)]:}, read));
  #endif
  /*@ loop_invariant 0 <= _w && _w <= WPT();
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write));
    loop_invariant (\forall int i; 0 <= i && i < _w; {:xvalues[i]:} ==
      LoadVector(i*get_global_size(1) + get_global_id(1), n, xgm, x_offset, x_inc, 1-is_rowmajor));*/
  // Loads the X-vector
  // #pragma unroll
  for (int _w = 0; _w < WPT; _w += 1) {
    const int id2 = _w*get_global_size(1) + get_global_id(1);
    xvalues[_w] = LoadVector(id2, n, xgm, x_offset, x_inc, 1-is_rowmajor);
  }

  #ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<n; Perm({:xgm[acc1d(i, x_offset, n, x_inc)]:}, read));
  #endif
  /*@ loop_invariant 0 <= _w && _w <= WPT();
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xtvalues[i]:}, write));
    loop_invariant (\forall int i; 0 <= i && i < _w; {:xtvalues[i]:} ==
      LoadVector(i*get_global_size(0) + get_global_id(0), n, xgm, x_offset, x_inc, is_rowmajor));*/
  // Loads the X-transposed-vector
  // #pragma unroll
  for (int _w = 0; _w < WPT; _w += 1) {
    const int id1 = _w*get_global_size(0) + get_global_id(0);
    xtvalues[_w] = LoadVector(id1, n, xgm, x_offset, x_inc, is_rowmajor);
  }

  #ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<n; Perm({:ygm[acc1d(i, y_offset, n, y_inc)]:}, read));
  #endif
  /*@ loop_invariant 0 <= _w && _w <= WPT();
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write));
    loop_invariant (\forall int i; 0 <= i && i < _w; {:yvalues[i]:} ==
      LoadVector(i*get_global_size(0) + get_global_id(0), n, ygm, y_offset, y_inc, is_rowmajor));*/
  // Loads the Y-vector
  // #pragma unroll
  for (int _w = 0; _w < WPT; _w += 1) {
    const int id1 = _w*get_global_size(0) + get_global_id(0);
    yvalues[_w] = LoadVector(id1, n, ygm, y_offset, y_inc, is_rowmajor);
  }

  #ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<n; Perm({:ygm[acc1d(i, y_offset, n, y_inc)]:}, read));
  #endif
  /*@ loop_invariant 0 <= _w && _w <= WPT();
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:ytvalues[i]:}, write));
    loop_invariant (\forall int i; 0 <= i && i < _w; {:ytvalues[i]:} ==
      LoadVector(i*get_global_size(1) + get_global_id(1), n, ygm, y_offset, y_inc, 1-is_rowmajor));*/
  // Loads the Y-transposed-vector
  //#pragma unroll
  for (int _w = 0; _w < WPT; _w += 1) {
    const int id2 = _w*get_global_size(1) + get_global_id(1);
    ytvalues[_w] = LoadVector(id2, n, ygm, y_offset, y_inc, 1-is_rowmajor);
  }

  // Sets the proper value of alpha in case conjugation is needed
  real alpha1 = alpha;
  real alpha2 = alpha;
  #if defined(ROUTINE_HER2) || defined(ROUTINE_HPR2)
    if (is_rowmajor) {
      COMPLEX_CONJUGATE(alpha1);
    }
    else {
      COMPLEX_CONJUGATE(alpha2);
    }
  #endif

  #ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<n; Perm({:xgm[acc1d(i, x_offset, n, x_inc)]:}, read));
  //@ loop_invariant (\forall* int i; 0 <=i && i<n; Perm({:ygm[acc1d(i, y_offset, n, y_inc)]:}, read));
  #endif
  /*@ loop_invariant 0 <= _w1 && _w1 <= WPT();
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write)); 
    loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xvalues[i]:} ==
      LoadVector(i*get_global_size(1) + get_global_id(1), n, xgm, x_offset, x_inc, 1-is_rowmajor));
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xtvalues[i]:}, write));
    loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xtvalues[i]:} ==
      LoadVector(i*get_global_size(0) + get_global_id(0), n, xgm, x_offset, x_inc, is_rowmajor));
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write)); 
    loop_invariant (\forall int i; 0 <= i && i < WPT(); {:yvalues[i]:} ==
      LoadVector(i*get_global_size(0) + get_global_id(0), n, ygm, y_offset, y_inc, is_rowmajor));
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:ytvalues[i]:}, write));
    loop_invariant (\forall int i; 0 <= i && i < WPT(); {:ytvalues[i]:} ==
      LoadVector(i*get_global_size(1) + get_global_id(1), n, ygm, y_offset, y_inc, 1-is_rowmajor));

    loop_invariant (\forall* int i, int j; 0 <= i && i < WPT() &&  0 <= j && j < WPT() &&
      i*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
      (\let int id1 = i*get_global_size(0) + get_global_id(0);
      (\let int id2 = j*get_global_size(1) + get_global_id(1);
        !((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) ==>
        Perm({:agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]:}, write))));
    loop_invariant (\forall* int i, int j; _w1 <= i && i < WPT() && 0 <= j && j < WPT() &&
        i*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
        (\let int id1 = i*get_global_size(0) + get_global_id(0);
        (\let int id2 = j*get_global_size(1) + get_global_id(1);
          !((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) ==>
          {:agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]:} ==
            \old(agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]))));
    loop_invariant (\forall* int i, int j; 0 <= i && i < _w1 && 0 <= j && j < WPT() &&
      i*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
      (\let int id1 = i*get_global_size(0) + get_global_id(0);
      (\let int id2 = j*get_global_size(1) + get_global_id(1);
        !((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) ==>
        {:agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]:} ==
          \old(agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]) + alpha1 * 
          LoadVector(id2, n, xgm, x_offset, x_inc, 1-is_rowmajor) *
          LoadVector(id1, n, ygm, y_offset, y_inc, is_rowmajor) + alpha2 *
          LoadVector(id1, n, xgm, x_offset, x_inc, is_rowmajor) *
          LoadVector(id2, n, ygm, y_offset, y_inc, 1-is_rowmajor))));
            */
  // Loops over the work per thread twice
  // #pragma unroll
  for (int _w1 = 0; _w1 < WPT; _w1 += 1) {
    #ifndef CONST_TYPES
    //@ loop_invariant (\forall* int i; 0 <=i && i<n; Perm({:xgm[acc1d(i, x_offset, n, x_inc)]:}, read));
    //@ loop_invariant (\forall* int i; 0 <=i && i<n; Perm({:ygm[acc1d(i, y_offset, n, y_inc)]:}, read));
    #endif
    /*@ loop_invariant 0 <= _w2 && _w2 <= WPT();
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write)); 
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xvalues[i]:} ==
        LoadVector(i*get_global_size(1) + get_global_id(1), n, xgm, x_offset, x_inc, 1-is_rowmajor));
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xtvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xtvalues[i]:} ==
        LoadVector(i*get_global_size(0) + get_global_id(0), n, xgm, x_offset, x_inc, is_rowmajor));
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write)); 
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:yvalues[i]:} ==
        LoadVector(i*get_global_size(0) + get_global_id(0), n, ygm, y_offset, y_inc, is_rowmajor));
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:ytvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:ytvalues[i]:} ==
        LoadVector(i*get_global_size(1) + get_global_id(1), n, ygm, y_offset, y_inc, 1-is_rowmajor));
      loop_invariant (\forall* int j; 0 <= j && j < WPT() &&
        _w1*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
        (\let int id1 = _w1*get_global_size(0) + get_global_id(0);
        (\let int id2 = j*get_global_size(1) + get_global_id(1);
          !((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) ==>
        Perm({:agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]:}, write))));
      loop_invariant (\forall* int j; _w2 <= j && j < WPT() &&
        _w1*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
        (\let int id1 = _w1*get_global_size(0) + get_global_id(0);
        (\let int id2 = j*get_global_size(1) + get_global_id(1);
          !((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) ==>
          {:agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]:} ==
            \old(agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]))));
      loop_invariant (\forall* int j; 0 <= j && j < _w2 &&
        _w1*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
        (\let int id1 = _w1*get_global_size(0) + get_global_id(0);
        (\let int id2 = j*get_global_size(1) + get_global_id(1);
          !((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) ==>
          {:agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]:} ==
            \old(agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]) + alpha1 * 
            LoadVector(id2, n, xgm, x_offset, x_inc, 1-is_rowmajor) *
            LoadVector(id1, n, ygm, y_offset, y_inc, is_rowmajor) + alpha2 *
            LoadVector(id1, n, xgm, x_offset, x_inc, is_rowmajor) *
            LoadVector(id2, n, ygm, y_offset, y_inc, 1-is_rowmajor))));
    */
    // #pragma unroll
    for (int _w2 = 0; _w2 < WPT; _w2 += 1) {

      // Global thread IDs
      const int id1 = _w1*get_global_size(0) + get_global_id(0);
      const int id2 = _w2*get_global_size(1) + get_global_id(1);

      // Skip these threads if they do not contain threads contributing to the matrix-triangle
      if ((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) {
        // Do nothing
      }

      // Loads A, performs the operation, and stores the result into A
      else {
        MatrixUpdate2(id1, id2, n, n, agm, a_offset, a_ld,
                      alpha1, xvalues[_w2], yvalues[_w1],
                      alpha2, xtvalues[_w1], ytvalues[_w2], is_upper);
      }
    }
  }
}

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
