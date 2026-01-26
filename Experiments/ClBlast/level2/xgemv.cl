#include "level2.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains the Xgemv kernel (generic version) for matrix-vector multiplication.
//
// =================================================================================================

// Enables loading of this file using the C++ pre-processor's #include (C++11 standard raw string
// literal). Comment-out this line for syntax-highlighting when developing.
//R"(

// =================================================================================================

// Parameters set by the tuner or by the database. Here they are given a basic default value in case
// this kernel file is used outside of the CLBlast library.

// 1: For the full version of the kernel
#ifndef WGS1
  // The local work-group size
#define WGS1 64     
  //@ inline pure int WGS1() = 64;
#endif
#ifndef WPT1
  // The amount of work-per-thread
#define WPT1 2      
  //@ inline pure int WPT1() = 2;
#endif
#ifndef UNROLL1
  // Unroll factor (must be a divider of WGS1)
#define UNROLL1 32  
  //@ inline pure int UNROLL1() = 32;
#endif

// 2 and 3: For the fast versions, see 'xgemv_fast.opencl'

// =================================================================================================

#ifndef CONST_TYPES
/*@ context agm != NULL ** (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
#endif
// Defines how to load the input matrix in the non-vectorized case
/*@ given int m; given int n;
  context agm != NULL && \pointer_length(agm) >= a_ld * n + a_offset;
  context 0 <= x && x < m;
  context 0 <= y && y < n;
  context a_ld >= m && a_offset >= 0;
  ensures \result == agm[acc2d(x, y, a_offset, m, n, a_ld)]; @*/
/*INLINE_FUNC*/ real LoadMatrixA(
  READ_ONLY1 real* restrict agm, const int x, const int y,
                             const int a_ld, const int a_offset, const int parameter,
                             const int kl, const int ku) {
  real result;

  // For banded matrices
  #if defined(ROUTINE_GBMV)
    const int k = ku - y;
    if (x >= y-ku && x < y+kl+1) { result = agm[a_ld*y + k + x + a_offset]; }
    else { SetToZero(result); }

  // For symmetric/hermitian matrices
  #elif defined(ROUTINE_HEMV) || defined(ROUTINE_SYMV)
    if ((parameter == 0 && y <= x) || (parameter == 1 && x <= y)) {
      result = agm[a_ld*y + x + a_offset];
      #if defined(ROUTINE_HEMV)
        if (x == y) { result.y = ZERO; }
      #endif
    }
    else {
      result = agm[a_ld*x + y + a_offset];
      #if defined(ROUTINE_HEMV)
        COMPLEX_CONJUGATE(result);
      #endif
    }

  // For triangular matrices
  #elif defined(ROUTINE_TRMV)
    if (((parameter == 0 || parameter == 2) && y <= x) ||
        ((parameter == 1 || parameter == 3) && x <= y)) {
      result = agm[a_ld*y + x + a_offset];
      if (parameter >= 2 && y == x) {
        SetToOne(result);
      }
    }
    else {
      SetToZero(result);
    }

  // For symmetric/hermitian banded matrices
  #elif defined(ROUTINE_HBMV) || defined(ROUTINE_SBMV)
    if (parameter == 1) {
      if (x <= y) {
        const int m = kl - y;
        if (x >= y-kl && x <= y) { result = agm[a_ld*y + m + x + a_offset]; }
        else { SetToZero(result); }
        #if defined(ROUTINE_HBMV)
          if (x == y) { result.y = ZERO; }
        #endif
      }
      else {
        const int m = kl - x;
        if (y >= x-kl && y <= x) { result = agm[a_ld*x + m + y + a_offset]; }
        else { SetToZero(result); }
        #if defined(ROUTINE_HBMV)
          COMPLEX_CONJUGATE(result);
        #endif
      }
    }
    else {
      if (x >= y) {
        const int m = -y;
        if (x >= y && x < y+kl+1) { result = agm[a_ld*y + m + x + a_offset]; }
        else { SetToZero(result); }
        #if defined(ROUTINE_HBMV)
          if (x == y) { result.y = ZERO; }
        #endif
      }
      else {
        const int m = -x;
        if (y >= x && y < x+kl+1) { result = agm[a_ld*x + m + y + a_offset]; }
        else { SetToZero(result); }
        #if defined(ROUTINE_HBMV)
          COMPLEX_CONJUGATE(result);
        #endif
      }
    }

  // For triangular banded matrices
  #elif defined(ROUTINE_TBMV)
    if (parameter == 1 || parameter == 3) {
      if (x <= y) {
        const int m = kl - y;
        if (x >= y-kl && x <= y) { result = agm[a_ld*y + m + x + a_offset]; }
        else { SetToZero(result); }
        if (parameter >= 2 && y == x) {
          SetToOne(result);
        }
      }
      else {
        SetToZero(result);
      }
    }
    else {
      if (x >= y) {
        const int m = -y;
        if (x >= y && x < y+kl+1) { result = agm[a_ld*y + m + x + a_offset]; }
        else { SetToZero(result); }
        if (parameter >= 2 && y == x) {
          SetToOne(result);
        }
      }
      else {
        SetToZero(result);
      }
    }

  // For symmetric/hermitian packed matrices
  #elif defined(ROUTINE_HPMV) || defined(ROUTINE_SPMV)
    if (parameter == 1) {
      if (x <= y) {
        result = agm[((y+1)*y)/2 + x + a_offset];
        #if defined(ROUTINE_HPMV)
          if (x == y) { result.y = ZERO; }
        #endif
      }
      else {
        result = agm[((x+1)*x)/2 + y + a_offset];
        #if defined(ROUTINE_HPMV)
          COMPLEX_CONJUGATE(result);
        #endif
      }
    }
    else {
      if (x >= y) {
        result = agm[((2*a_ld-(y+1))*y)/2 + x + a_offset];
        #if defined(ROUTINE_HPMV)
          if (x == y) { result.y = ZERO; }
        #endif
      }
      else {
        result = agm[((2*a_ld-(x+1))*x)/2 + y + a_offset];
        #if defined(ROUTINE_HPMV)
          COMPLEX_CONJUGATE(result);
        #endif
      }
    }

  // For triangular packed matrices
  #elif defined(ROUTINE_TPMV)
    if (parameter == 1 || parameter == 3) {
      if (x <= y) {
        result = agm[((y+1)*y)/2 + x + a_offset];
        if (parameter >= 2 && y == x) {
          SetToOne(result);
        }
      }
      else {
        SetToZero(result);
      }
    }
    else {
      if (x >= y) {
        result = agm[((2*a_ld-(y+1))*y)/2 + x + a_offset];
        if (parameter >= 2 && y == x) {
          SetToOne(result);
        }
      }
      else {
        SetToZero(result);
      }
    }

  // For general matrices
  #else
    int idx = a_ld*y + x + a_offset;
    //@ assert idx == acc2d(x, y, a_offset, m, n, a_ld);
    result = agm[idx];
  #endif

  return result;
}

// =================================================================================================

#ifdef EXTRACT_BODY
/*@ extract_body */
#endif
#ifndef CONST_TYPES
/*@ context xgm!=NULL ** (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
  context agm!=NULL ** (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
#endif
/*@
  context get_num_groups(0) == 10 && get_num_groups(1) == 1 && get_num_groups(2) == 1;
  context get_local_size(0) == WGS1() && get_local_size(1) == 1 && get_local_size(2) == 1;
  context n >= 1 && m >= 1;
  context x_inc >= 1 && x_offset >= 0;
  context xgm != NULL && \pointer_length(xgm) >= n*x_inc+x_offset;
  context y_inc >= 1 && y_offset >= 0;
  context ygm != NULL && \pointer_length(ygm) >= m*y_inc+y_offset;
  context agm != NULL && a_offset >= 0;
  context a_rotated == 0 ==> a_ld >= m &&\pointer_length(agm) >= a_ld * n + a_offset;
  context a_rotated != 0 ==> a_ld >= n &&\pointer_length(agm) >= a_ld * m + a_offset;

  context (\forall* int i; 0 <= i && i < WPT1()
    && \gtid + i*get_global_size(0) < m;
      Perm({:ygm[acc1d(\gtid + i*get_global_size(0), y_offset, m, y_inc)]:}, write));

  requires Perm({:xlm[\ltid]:}, write);@*/
// The main reduction kernel, performing the multiplication and the majority of the sum operation
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(WGS1, 1, 1)))
#endif
void Xgemv(const int m, const int n,
                    const real_arg arg_alpha,
                    const real_arg arg_beta,
                    const int a_rotated,
                    READ_ONLY1 __global real* restrict agm, const int a_offset, const int a_ld,
                    READ_ONLY2 __global real* restrict xgm, const int x_offset, const int x_inc,
                    UNIQUE3 __global real* ygm, const int y_offset, const int y_inc,
                    const int do_conjugate, const int parameter,
                    const int kl, const int ku) {
  const real alpha = GetRealArg(arg_alpha);
  const real beta = GetRealArg(arg_beta);

  // Local memory for the vector X
  UNIQUE4 __local real xlm[WGS1];

  // Initializes the accumulation register
  // #pragma promote_to_registers
  real acc1[WPT1];
  //#pragma unroll
  /*@
    loop_invariant 0 <= _w && _w <= WPT1();
    loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
    loop_invariant (\forall int j; 0 <= j && j < _w; {:acc1[j]:} == 0);
  @*/
  for (int _w = 0; _w < WPT1; _w += 1) {
    SetToZero(acc1[_w]);
  }

  // Divides the work in a main and tail section
  const int n_tail = n % WGS1;
  const int n_floor = n - n_tail;
  //@ ghost int id_i = 0;
  // Loops over work-group sized portions of the work
#ifndef CONST_TYPES
/*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
    loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
#endif
/*@ loop_invariant 0 <= kwg && kwg < n_floor + WGS1();
    loop_invariant kwg == id_i * WGS1();
    loop_invariant kwg % WGS1() == 0;
    loop_invariant 0 <= id_i && id_i <= n_floor / WGS1();
    loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
    loop_invariant Perm({:xlm[\ltid]:}, write);

    loop_invariant kwg==0 ==> (\forall* int j; 0 <= j && j < WPT1(); {:acc1[j]:} == 0);@*/
  for (int kwg=0; kwg<n_floor; kwg+=WGS1) {

    // Loads the vector X into local memory
    const int lid = get_local_id(0);
    int xid = (kwg + lid)*x_inc + x_offset;
    //@ assert xid == acc1d(kwg + lid, x_offset, n, x_inc);
    xlm[lid] = xgm[xid];

#ifndef CONST_TYPES
/*@ context (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));*/
#endif
  /*@ context 0 <= kwg && kwg < n_floor && n_floor == n - n % WGS1();
      context x_offset >= 0 && x_inc >= 1;
      requires Perm({:xlm[\ltid]:}, write);
      requires {:xlm[\ltid]:} == xgm[acc1d(kwg + \ltid, x_offset, n, x_inc)];
      ensures (\forall* int i; 0 <= i && i < WGS1(); Perm({:xlm[i]:}, write\WGS1()));
      ensures (\forall int i; 0 <= i && i < WGS1(); {:xlm[i]:} == xgm[acc1d(kwg + i, x_offset, n, x_inc)]);@*/
    // Synchronizes all threads in a workgroup
    barrier(CLK_LOCAL_MEM_FENCE);

    #ifndef CONST_TYPES
  /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
      loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
    #endif
  /*@ loop_invariant 0 <= _w && _w <= WPT1();
      loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
      loop_invariant (\forall* int i; 0 <= i && i < WGS1(); Perm({:xlm[i]:}, write\WGS1()));
      loop_invariant (\forall int i; 0 <= i && i < WGS1(); {:xlm[i]:} == xgm[acc1d(kwg + i, x_offset, n, x_inc)]); @*/
    // Loops over the work per thread, and checks whether in bounds
    //#pragma unroll
    for (int _w = 0; _w < WPT1; _w += 1) {
      const int gid = _w*get_global_size(0) + get_global_id(0);
      if (gid < m) {

        // The multiply-add function for the main part (divisable by WGS1)
        if (a_rotated == 0) { // Not rotated
          #ifndef CONST_TYPES
          /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
            loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
          #endif
          /*@ loop_invariant 0 <= kloop && kloop <= WGS1();
            loop_invariant kloop % UNROLL1() == 0;
            loop_invariant (\forall* int j; 0 <= j && j < WGS1(); Perm({:xlm[j]:}, write\WGS1()));
            loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
            loop_invariant (\forall int i; 0 <= i && i < WGS1(); {:xlm[i]:} == xgm[acc1d(kwg + i, x_offset, n, x_inc)]);@*/
          for (int kloop=0; kloop<WGS1; kloop+=UNROLL1) {
            #ifndef CONST_TYPES
            /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
              loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
            #endif
            /*@ loop_invariant 0 <= _kunroll && _kunroll <= UNROLL1();
              loop_invariant (\forall* int j; 0 <= j && j < WGS1(); Perm({:xlm[j]:}, write\WGS1()));
              loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
              loop_invariant (\forall int i; 0 <= i && i < WGS1(); {:xlm[i]:} == xgm[acc1d(kwg + i, x_offset, n, x_inc)]);@*/
            //#pragma unroll
            for (int _kunroll = 0; _kunroll < UNROLL1; _kunroll += 1) {
              const int k = kwg + kloop + _kunroll;
              real value = LoadMatrixA(agm, gid, k, a_ld, a_offset, parameter, kl, ku) /*@given {m=m, n=n} @*/;
              if (do_conjugate == 1) { COMPLEX_CONJUGATE(value); }
              MultiplyAdd(acc1[_w], xlm[kloop + _kunroll], value);
            }
          }
        }
        else { // Transposed
          #ifndef CONST_TYPES
          /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
            loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
          #endif
          /*@ loop_invariant 0 <= kloop && kloop <= WGS1();
            loop_invariant kloop % UNROLL1() == 0;
            loop_invariant (\forall* int j; 0 <= j && j < WGS1(); Perm({:xlm[j]:}, write\WGS1()));
            loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
            loop_invariant (\forall int i; 0 <= i && i < WGS1(); {:xlm[i]:} == xgm[acc1d(kwg + i, x_offset, n, x_inc)]);@*/
          for (int kloop=0; kloop<WGS1; kloop+=UNROLL1) {
            #ifndef CONST_TYPES
            /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
              loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
            #endif
            /*@ loop_invariant 0 <= _kunroll && _kunroll <= UNROLL1();
              loop_invariant (\forall* int j; 0 <= j && j < WGS1(); Perm({:xlm[j]:}, write\WGS1()));
              loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
              loop_invariant (\forall int i; 0 <= i && i < WGS1(); {:xlm[i]:} == xgm[acc1d(kwg + i, x_offset, n, x_inc)]);@*/
            //#pragma unroll
            for (int _kunroll = 0; _kunroll < UNROLL1; _kunroll += 1) {
              const int k = kwg + kloop + _kunroll;
              real value = LoadMatrixA(agm, k, gid, a_ld, a_offset, parameter, kl, ku)  /*@given {m=n, n=m} @*/;
              if (do_conjugate == 1) { COMPLEX_CONJUGATE(value); }
              MultiplyAdd(acc1[_w], xlm[kloop + _kunroll], value);
            }
          }
        }
      }
    }

    // // Synchronizes all threads in a workgroup
    /*@
      requires (\forall* int i; 0 <= i && i < WGS1(); Perm({:xlm[i]:}, write\WGS1()));
      ensures Perm({:xlm[\ltid]:}, write);
    @*/
    barrier(CLK_LOCAL_MEM_FENCE);
    //@ ghost id_i++;
  }

#ifndef CONST_TYPES
/*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
    loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
#endif
/*@ loop_invariant 0 <= _w && _w <= WPT1();
    loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
    loop_invariant (\forall* int i; 0 <= i && i < WPT1()
      && \gtid + i*get_global_size(0) < m;
        Perm({:ygm[acc1d(\gtid + i*get_global_size(0), y_offset, m, y_inc)]:}, write)); @*/
  // Loops over the work per thread, and checks whether in bounds
  //#pragma unroll
  for (int _w = 0; _w < WPT1; _w += 1) {
    const int gid = _w*get_global_size(0) + get_global_id(0);
    if (gid < m) {

      // The multiply-add function for the remainder part (not divisable by WGS1)
      if (a_rotated == 0) { // Not rotated
      #ifndef CONST_TYPES
      /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
          loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
      #endif
      /*@ loop_invariant n_floor <= k && k <= n;
          loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
        @*/
        for (int k=n_floor; k<n; ++k) {
          real value = LoadMatrixA(agm, gid, k, a_ld, a_offset, parameter, kl, ku) /*@given {m=m, n=n} @*/;
          if (do_conjugate == 1) { COMPLEX_CONJUGATE(value); }
          int xid = k*x_inc + x_offset;
          //@ assert xid == acc1d(k, x_offset, n, x_inc);
          MultiplyAdd(acc1[_w], xgm[xid], value);
        }
      }
      else { // Transposed
        #ifndef CONST_TYPES
        /*@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
            loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(agm); Perm({:agm[i]:}, read)); */
        #endif
        /*@ 
          loop_invariant n_floor <= k && k <= n;
          loop_invariant (\forall* int j; 0 <= j && j < WPT1(); Perm({:acc1[j]:}, write));
        @*/
        for (int k=n_floor; k<n; ++k) {
          real value = LoadMatrixA(agm, k, gid, a_ld, a_offset, parameter, kl, ku) /*@given {m=n, n=m} @*/;
          if (do_conjugate == 1) { COMPLEX_CONJUGATE(value); }
          int xid = k*x_inc + x_offset;
          //@ assert xid == acc1d(k, x_offset, n, x_inc);
          MultiplyAdd(acc1[_w], xgm[xid], value);
        }
      }

      // Stores the final result
      int yid = gid*y_inc + y_offset;
      //@ assert yid == acc1d(gid, y_offset, m, y_inc);
      real yval = ygm[yid];
      AXPBY(ygm[yid], alpha, acc1[_w], beta, yval);
    }
  }
}

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
