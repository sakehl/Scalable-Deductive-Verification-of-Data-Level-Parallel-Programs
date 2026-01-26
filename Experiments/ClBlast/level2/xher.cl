#include "level2.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains the Xher kernels for rank-1 matrix update.
//
// =================================================================================================

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
  context n >= 1 && n >= 1;
  context x_inc >= 1 && x_offset >= 0;
  context xgm != NULL && \pointer_length(xgm) >= n*x_inc+x_offset;
  context agm != NULL && a_offset >= 0;
  context is_rowmajor == 0 || is_rowmajor == 1;
  context a_ld >= n && \pointer_length(agm) >= a_ld * n + a_offset;

  context (\forall* int i, int j; 0 <= i && i < WPT() &&  0 <= j && j < WPT() &&
    i*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
    Perm({:agm[acc2d(i*get_global_size(0) + get_global_id(0), 
                   j*get_global_size(1) + get_global_id(1),
                   a_offset, a_ld, n, a_ld)]:}, write));*/
#ifndef CONST_TYPES
/*@ context xgm!=NULL ** (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));*/
#endif
/*@ ensures (\forall* int i, int j; 0 <= i && i < WPT() && 0 <= j && j < WPT() &&
    i*get_global_size(0) + get_global_id(0) < n && j*get_global_size(1) + get_global_id(1) < n;
    (\let int id1 = i*get_global_size(0) + get_global_id(0);
    (\let int id2 = j*get_global_size(1) + get_global_id(1);
    !((is_upper!=0 && (id1 > id2)) || (is_upper==0 && (id2 > id1))) ==>
      {:agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]:} ==
        \old(agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]) + arg_alpha * 
        xgm[acc1d(id1, x_offset, n, x_inc)]*
        xgm[acc1d(id2, x_offset, n, x_inc)])));*/
// Symmetric version of the rank-1 matrix update kernel (HER, HPR, SYR, SPR)
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(WGS1, 1, 1)))
#endif
void Xher(const int n,
          const real_arg arg_alpha,
          READ_ONLY1 __global real* restrict xgm, const int x_offset, const int x_inc,
          UNIQUE2 __global real* restrict agm, const int a_offset, const int a_ld,
          const int is_upper, const int is_rowmajor) {
  const real alpha = GetRealArg(arg_alpha);

  // Register storage for X and XT
  // #pragma promote_to_registers
  UNIQUE3 real xvalues[WPT];
  // #pragma promote_to_registers
  UNIQUE4 real xtvalues[WPT];

  #ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
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
  //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
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
  //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
  #endif
  /*@ loop_invariant 0 <= _w1 && _w1 <= WPT();
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xtvalues[i]:}, write));
    loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xtvalues[i]:} ==
      LoadVector(i*get_global_size(0) + get_global_id(0), n, xgm, x_offset, x_inc, is_rowmajor));
    loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write)); 
    loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xvalues[i]:} ==
      LoadVector(i*get_global_size(1) + get_global_id(1), n, xgm, x_offset, x_inc, 1-is_rowmajor));
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
            \old(agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]) + alpha * 
            LoadVector(id1, n, xgm, x_offset, x_inc, is_rowmajor) *
            LoadVector(id2, n, xgm, x_offset, x_inc, 1-is_rowmajor)))); */
  // Loops over the work per thread twice
  // #pragma unroll
  for (int _w1 = 0; _w1 < WPT; _w1 += 1) {
    #ifndef CONST_TYPES
    //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
    #endif
    /*@ loop_invariant 0 <= _w2 && _w2 <= WPT();
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xtvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xtvalues[i]:} ==
        LoadVector(i*get_global_size(0) + get_global_id(0), n, xgm, x_offset, x_inc, is_rowmajor));
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write)); 
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xvalues[i]:} ==
        LoadVector(i*get_global_size(1) + get_global_id(1), n, xgm, x_offset, x_inc, 1-is_rowmajor));
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
            \old(agm[acc2d(id1, id2, a_offset, a_ld, n, a_ld)]) + alpha * 
            LoadVector(id1, n, xgm, x_offset, x_inc, is_rowmajor) *
            LoadVector(id2, n, xgm, x_offset, x_inc, 1-is_rowmajor))));
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
        MatrixUpdate(id1, id2, n, n, agm, a_offset, a_ld, alpha, xvalues[_w2], xtvalues[_w1], is_upper);
      }
    }
  }
}

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
