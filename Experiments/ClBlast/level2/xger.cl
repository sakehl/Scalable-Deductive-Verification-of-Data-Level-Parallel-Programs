#include "level2.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains the Xger kernels for rank-1 matrix update.
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
  context max2 >= 1 && max1 >= 1;
  context x_inc >= 1 && x_offset >= 0 && xgm != NULL;

  context y_inc >= 1 && y_offset >= 0 && ygm != NULL;
  context is_rowmajor != 0 ==> \pointer_length(xgm) >= max2*x_inc+x_offset && \pointer_length(ygm) >= max1*y_inc+y_offset;
  context is_rowmajor == 0 ==> \pointer_length(xgm) >= max1*x_inc+x_offset && \pointer_length(ygm) >= max2*y_inc+y_offset;
  context agm != NULL && a_offset >= 0 && a_ld >= max1 && \pointer_length(agm) >= a_ld * max2 + a_offset;

  context (\forall* int i, int j; 0 <= i && i < WPT() &&  0 <= j && j < WPT() &&
    i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
    Perm({:agm[acc2d(i*get_global_size(0) + get_global_id(0), 
                   j*get_global_size(1) + get_global_id(1),
                   a_offset, a_ld, max2, a_ld)]:}, write));*/
#ifndef CONST_TYPES
/*@ context (\forall* int i; 0 <= i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
  context (\forall* int i; 0 <= i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read)); */
#endif
/*@ ensures (\forall* int i, int j; is_rowmajor != 0 && 0 <= i && i < WPT() && 0 <= j && j < WPT() &&
    i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
    (\let int id1 = i*get_global_size(0) + get_global_id(0);
    (\let int id2 = j*get_global_size(1) + get_global_id(1);
      {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
        \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]) + arg_alpha * 
        ygm[acc1d(id1, y_offset, max1, y_inc)]*
        xgm[acc1d(id2, x_offset, max2, x_inc)])));
  ensures (\forall* int i, int j; is_rowmajor == 0 && 0 <= i && i < WPT() && 0 <= j && j < WPT() &&
    i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
    (\let int id1 = i*get_global_size(0) + get_global_id(0);
    (\let int id2 = j*get_global_size(1) + get_global_id(1);
      {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
        \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]) + arg_alpha * 
        LoadVector(id2, max2, ygm, y_offset, y_inc, 1) *
        LoadVector(id1, max1, xgm, x_offset, x_inc, 0))));@*/
// Regular version of the rank-1 matrix update kernel (GER, GERU, GERC)
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(WGS1, 1, 1)))
#endif
void Xger(const int max1, const int max2,
          const real_arg arg_alpha,
          READ_ONLY1 __global real* restrict xgm, const int x_offset, const int x_inc,
          READ_ONLY2 __global real* ygm, const int y_offset, const int y_inc,
          UNIQUE3 __global real* restrict agm, const int a_offset, const int a_ld,
          const int is_rowmajor) {
  const real alpha = GetRealArg(arg_alpha);

  // Register storage for X and Y
  // #pragma promote_to_registers
  UNIQUE4 real xvalues[WPT];
  // #pragma promote_to_registers
  UNIQUE5 real yvalues[WPT];

  // Row-major version
  if (is_rowmajor != 0) {

    #ifndef CONST_TYPES
    /*@ loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));*/
    #endif
    /*@ loop_invariant 0 <= _w && _w <= WPT();
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < _w; {:xvalues[i]:} ==
        LoadVector(i*get_global_size(1) + get_global_id(1), max2, xgm, x_offset, x_inc, 0));*/
    // Loads the X-vector
    // #pragma unroll
    for (int _w = 0; _w < WPT; _w += 1) {
      const int id2 = _w*get_global_size(1) + get_global_id(1);
      xvalues[_w] = LoadVector(id2, max2, xgm, x_offset, x_inc, false);
    }
    
    #ifndef CONST_TYPES
    /*@ loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));*/
    #endif
    /*@ loop_invariant 0 <= _w && _w <= WPT();
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < _w; {:yvalues[i]:} ==
        LoadVector(i*get_global_size(0) + get_global_id(0), max1, ygm, y_offset, y_inc, 1));*/
    // Loads the Y-vector
    //#pragma unroll
    for (int _w = 0; _w < WPT; _w += 1) {
      const int id1 = _w*get_global_size(0) + get_global_id(0);
      yvalues[_w] = LoadVector(id1, max1, ygm, y_offset, y_inc, true);
    }

    #ifndef CONST_TYPES
    /*@ loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
      loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));*/
    #endif
    /*@ loop_invariant 0 <= _w1 && _w1 <= WPT();
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:yvalues[i]:} ==
        LoadVector(i*get_global_size(0) + get_global_id(0), max1, ygm, y_offset, y_inc, 1));
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write)); 
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xvalues[i]:} ==
        LoadVector(i*get_global_size(1) + get_global_id(1), max2, xgm, x_offset, x_inc, 0));
      loop_invariant (\forall* int i, int j; 0 <= i && i < WPT() &&  0 <= j && j < WPT() &&
        i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
        Perm({:agm[acc2d(i*get_global_size(0) + get_global_id(0), 
                      j*get_global_size(1) + get_global_id(1),
                      a_offset, a_ld, max2, a_ld)]:}, write));
      loop_invariant (\forall* int i, int j; _w1 <= i && i < WPT() && 0 <= j && j < WPT() &&
          i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          (\let int id1 = i*get_global_size(0) + get_global_id(0);
          (\let int id2 = j*get_global_size(1) + get_global_id(1);
            {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
              \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]))));
      loop_invariant (\forall* int i, int j; 0 <= i && i < _w1 && 0 <= j && j < WPT() &&
          i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          (\let int id1 = i*get_global_size(0) + get_global_id(0);
          (\let int id2 = j*get_global_size(1) + get_global_id(1);
            {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
              \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]) + alpha * 
              LoadVector(id1, max1, ygm, y_offset, y_inc, 1) *
              LoadVector(id2, max2, xgm, x_offset, x_inc, 0)))); */
    // Loops over the work per thread twice
    //#pragma unroll
    for (int _w1 = 0; _w1 < WPT; _w1 += 1) {
      #ifndef CONST_TYPES
      /*@ loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
          loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));*/
      #endif
      /*@ loop_invariant 0 <= _w2 && _w2 <= WPT();
        loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write));
        loop_invariant (\forall int i; 0 <= i && i < WPT(); {:yvalues[i]:} ==
          LoadVector(i*get_global_size(0) + get_global_id(0), max1, ygm, y_offset, y_inc, 1));
        loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write)); 
        loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xvalues[i]:} ==
          LoadVector(i*get_global_size(1) + get_global_id(1), max2, xgm, x_offset, x_inc, 0));
        loop_invariant (\forall* int j; 0 <= j && j < WPT() &&
          _w1*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          Perm({:agm[acc2d(_w1*get_global_size(0) + get_global_id(0), 
                        j*get_global_size(1) + get_global_id(1),
                        a_offset, a_ld, max2, a_ld)]:}, write));
        loop_invariant (\forall* int j; _w2 <= j && j < WPT() &&
          _w1*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          (\let int id1 = _w1*get_global_size(0) + get_global_id(0);
          (\let int id2 = j*get_global_size(1) + get_global_id(1);
            {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
              \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]))));
        loop_invariant (\forall* int j; 0 <= j && j < _w2 &&
          _w1*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          (\let int id1 = _w1*get_global_size(0) + get_global_id(0);
          (\let int id2 = j*get_global_size(1) + get_global_id(1);
            {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
              \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]) + alpha * 
              LoadVector(id1, max1, ygm, y_offset, y_inc, 1) *
              LoadVector(id2, max2, xgm, x_offset, x_inc, 0))));
      */
      //#pragma unroll
      for (int _w2 = 0; _w2 < WPT; _w2 += 1) {

        // Global thread IDs
        const int id1 = _w1*get_global_size(0) + get_global_id(0);
        const int id2 = _w2*get_global_size(1) + get_global_id(1);

        // Loads A, performs the operation, and stores the result into A
        MatrixUpdate(id1, id2, max1, max2, agm, a_offset, a_ld,
                     alpha, xvalues[_w2], yvalues[_w1], false);
      }
    }
  }

  // Col-major version
  else {
    #ifndef CONST_TYPES
    /*@ loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));*/
    #endif
    /*@ loop_invariant 0 <= _w && _w <= WPT();
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < _w; {:xvalues[i]:} ==
        LoadVector(i*get_global_size(0) + get_global_id(0), max1, xgm, x_offset, x_inc, 0));*/
    // Loads the X-vector
    // #pragma unroll
    for (int _w = 0; _w < WPT; _w += 1) {
      const int id1 = _w*get_global_size(0) + get_global_id(0);
      xvalues[_w] = LoadVector(id1, max1, xgm, x_offset, x_inc, false);
    }

    #ifndef CONST_TYPES
    /*@ loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));*/
    #endif
    /*@ loop_invariant 0 <= _w && _w <= WPT();
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < _w; {:yvalues[i]:} ==
        LoadVector(i*get_global_size(1) + get_global_id(1), max2, ygm, y_offset, y_inc, 1));*/
    // Loads the Y-vector
    //#pragma unroll
    for (int _w = 0; _w < WPT; _w += 1) {
      const int id2 = _w*get_global_size(1) + get_global_id(1);
      yvalues[_w] = LoadVector(id2, max2, ygm, y_offset, y_inc, true);
    }

    #ifndef CONST_TYPES
    /*@ loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
      loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));*/
    #endif
    /*@ loop_invariant 0 <= _w1 && _w1 <= WPT();
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write));
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:yvalues[i]:} ==
        LoadVector(i*get_global_size(1) + get_global_id(1), max2, ygm, y_offset, y_inc, 1));
      loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write)); 
      loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xvalues[i]:} ==
        LoadVector(i*get_global_size(0) + get_global_id(0), max1, xgm, x_offset, x_inc, 0));
      loop_invariant (\forall* int i, int j; 0 <= i && i < WPT() &&  0 <= j && j < WPT() &&
        i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
        Perm({:agm[acc2d(i*get_global_size(0) + get_global_id(0), 
                      j*get_global_size(1) + get_global_id(1),
                      a_offset, a_ld, max2, a_ld)]:}, write));
      loop_invariant (\forall* int i, int j; _w1 <= i && i < WPT() && 0 <= j && j < WPT() &&
          i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          (\let int id1 = i*get_global_size(0) + get_global_id(0);
          (\let int id2 = j*get_global_size(1) + get_global_id(1);
            {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
              \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]))));
      loop_invariant (\forall* int i, int j; 0 <= i && i < _w1 && 0 <= j && j < WPT() &&
          i*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          (\let int id1 = i*get_global_size(0) + get_global_id(0);
          (\let int id2 = j*get_global_size(1) + get_global_id(1);
            {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
              \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]) + alpha * 
              LoadVector(id2, max2, ygm, y_offset, y_inc, 1) *
              LoadVector(id1, max1, xgm, x_offset, x_inc, 0))));
              */
    // Loops over the work per thread twice
    //#pragma unroll
    for (int _w1 = 0; _w1 < WPT; _w1 += 1) {
      #ifndef CONST_TYPES
      /*@ loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
        loop_invariant (\forall* int i; 0 <= i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));*/
      #endif
      /*@ loop_invariant 0 <= _w2 && _w2 <= WPT();
        loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:yvalues[i]:}, write));
        loop_invariant (\forall int i; 0 <= i && i < WPT(); {:yvalues[i]:} ==
          LoadVector(i*get_global_size(1) + get_global_id(1), max2, ygm, y_offset, y_inc, 1));
        loop_invariant (\forall* int i; 0 <= i && i < WPT(); Perm({:xvalues[i]:}, write)); 
        loop_invariant (\forall int i; 0 <= i && i < WPT(); {:xvalues[i]:} ==
          LoadVector(i*get_global_size(0) + get_global_id(0), max1, xgm, x_offset, x_inc, 0));
        loop_invariant (\forall* int j; 0 <= j && j < WPT() &&
          _w1*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          Perm({:agm[acc2d(_w1*get_global_size(0) + get_global_id(0), 
                        j*get_global_size(1) + get_global_id(1),
                        a_offset, a_ld, max2, a_ld)]:}, write));
        loop_invariant (\forall* int j; _w2 <= j && j < WPT() &&
          _w1*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          (\let int id1 = _w1*get_global_size(0) + get_global_id(0);
          (\let int id2 = j*get_global_size(1) + get_global_id(1);
            {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
              \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]))));
        loop_invariant (\forall* int j; 0 <= j && j < _w2 &&
          _w1*get_global_size(0) + get_global_id(0) < max1 && j*get_global_size(1) + get_global_id(1) < max2;
          (\let int id1 = _w1*get_global_size(0) + get_global_id(0);
          (\let int id2 = j*get_global_size(1) + get_global_id(1);
            {:agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]:} ==
              \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]) + alpha * 
              LoadVector(id2, max2, ygm, y_offset, y_inc, 1) *
              LoadVector(id1, max1, xgm, x_offset, x_inc, 0))));
      */
      //#pragma unroll
      for (int _w2 = 0; _w2 < WPT; _w2 += 1) {

        // Global thread IDs
        const int id1 = _w1*get_global_size(0) + get_global_id(0);
        const int id2 = _w2*get_global_size(1) + get_global_id(1);

        // Loads A, performs the operation, and stores the result into A
        MatrixUpdate(id1, id2, max1, max2, agm, a_offset, a_ld,
                     alpha, xvalues[_w1], yvalues[_w2], false);
      }
    }
  }
}

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
