#include "level1.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains the Xhad kernel. It contains one fast vectorized version in case of unit
// strides (incx=incy=incz=1) and no offsets (offx=offy=offz=0). Another version is more general,
// but doesn't support vector data-types. Based on the XAXPY kernels.
//
// This kernel uses the level-1 BLAS common tuning parameters.
//
// =================================================================================================

// Enables loading of this file using the C++ pre-processor's #include (C++11 standard raw string
// literal). Comment-out this line for syntax-highlighting when developing.
//R"(

// =================================================================================================

// A vector-vector multiply function. See also level1.opencl for a vector-scalar version
INLINE_FUNC realV MultiplyVectorVector(realV cvec, const realV aval, const realV bvec) {
  #if VW == 1
    Multiply(cvec, aval, bvec);
  #elif VW == 2
    Multiply(cvec.x, aval.x, bvec.x);
    Multiply(cvec.y, aval.y, bvec.y);
  #elif VW == 4
    Multiply(cvec.x, aval.x, bvec.x);
    Multiply(cvec.y, aval.y, bvec.y);
    Multiply(cvec.z, aval.z, bvec.z);
    Multiply(cvec.w, aval.w, bvec.w);
  #elif VW == 8
    Multiply(cvec.s0, aval.s0, bvec.s0);
    Multiply(cvec.s1, aval.s1, bvec.s1);
    Multiply(cvec.s2, aval.s2, bvec.s2);
    Multiply(cvec.s3, aval.s3, bvec.s3);
    Multiply(cvec.s4, aval.s4, bvec.s4);
    Multiply(cvec.s5, aval.s5, bvec.s5);
    Multiply(cvec.s6, aval.s6, bvec.s6);
    Multiply(cvec.s7, aval.s7, bvec.s7);
  #elif VW == 16
    Multiply(cvec.s0, aval.s0, bvec.s0);
    Multiply(cvec.s1, aval.s1, bvec.s1);
    Multiply(cvec.s2, aval.s2, bvec.s2);
    Multiply(cvec.s3, aval.s3, bvec.s3);
    Multiply(cvec.s4, aval.s4, bvec.s4);
    Multiply(cvec.s5, aval.s5, bvec.s5);
    Multiply(cvec.s6, aval.s6, bvec.s6);
    Multiply(cvec.s7, aval.s7, bvec.s7);
    Multiply(cvec.s8, aval.s8, bvec.s8);
    Multiply(cvec.s9, aval.s9, bvec.s9);
    Multiply(cvec.sA, aval.sA, bvec.sA);
    Multiply(cvec.sB, aval.sB, bvec.sB);
    Multiply(cvec.sC, aval.sC, bvec.sC);
    Multiply(cvec.sD, aval.sD, bvec.sD);
    Multiply(cvec.sE, aval.sE, bvec.sE);
    Multiply(cvec.sF, aval.sF, bvec.sF);
  #endif
  return cvec;
}

#if VW == 1
/*@ pure float XhadPure(float z, float alpha, float x, float beta, float y) =
  z * beta + (alpha * x) * y;
@*/
#endif

// =================================================================================================

// Full version of the kernel with offsets and strided accesses
#ifdef EXTRACT_BODY
/*@ extract_body */
#endif
#ifndef CONST_TYPES
//@ context xgm != NULL ** (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
//@ context ygm != NULL ** (\forall* int i; 0 <=i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));
#endif
/*@
  context get_local_size(0) == WGS() && get_local_size(1) == 1 && get_local_size(2) == 1;
  context get_num_groups(0) == 10 && get_num_groups(1) == 1 && get_num_groups(2) == 1;
  context n >= 1 && x_inc >= 1 && x_offset >= 0
    && y_inc >= 1 && y_offset >= 0
    && z_inc >= 1 && z_offset >= 0;
  context xgm != NULL && \pointer_length(xgm) >= n*x_inc+x_offset;
  context ygm != NULL && \pointer_length(ygm) >= n*y_inc+y_offset;
  context zgm != NULL && \pointer_length(zgm) >= n*z_inc+z_offset;
  context (\forall* int i; 0 <= i && i < (n-1)/(get_global_size(0))+1 
    && \gtid + i*get_global_size(0) < n;
      Perm({:zgm[acc1d(\gtid + i*get_global_size(0), z_offset, n, z_inc)]:}, write));
  ensures (\forall int i; 0 <= i && i < (n-1)/(get_global_size(0))+1
      && \gtid + i*get_global_size(0) < n;
        {:zgm[acc1d(\gtid + i*get_global_size(0), z_offset, n, z_inc)]:} ==
        XhadPure(\old(zgm[acc1d(\gtid + i*get_global_size(0), z_offset, n, z_inc)]), arg_alpha, xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)], arg_beta, 
        ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]));
@*/
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(WGS, 1, 1)))
#endif
void Xhad(const int n, const real_arg arg_alpha, const real_arg arg_beta,
          READ_ONLY1 __global real* restrict xgm, const int x_offset, const int x_inc,
          READ_ONLY2 __global real* restrict ygm, const int y_offset, const int y_inc,
          UNIQUE3 __global real* zgm, const int z_offset, const int z_inc
  ) {
  const real alpha = GetRealArg(arg_alpha);
  const real beta = GetRealArg(arg_beta);

  //@ ghost int id_i = 0;
  // Loops over the work that needs to be done (allows for an arbitrary number of threads)
#ifndef CONST_TYPES
  //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(xgm); Perm({:xgm[i]:}, read));
  //@ loop_invariant (\forall* int i; 0 <=i && i<\pointer_length(ygm); Perm({:ygm[i]:}, read));
#endif
  /*@
    loop_invariant \gtid <= id && id < n + get_global_size(0);
    loop_invariant id == \gtid + id_i * get_global_size(0);
    loop_invariant id % get_global_size(0) == \gtid;
    loop_invariant 0 <= id_i && id_i <= (n-1)/(get_global_size(0))+1;

    loop_invariant (\forall* int i; 0 <= i && i < (n-1)/(get_global_size(0))+1 
      && \gtid + i*get_global_size(0) < n;
        Perm({:zgm[acc1d(\gtid + i*get_global_size(0), z_offset, n, z_inc)]:}, write));
    loop_invariant (\forall int i; id_i <= i && i < (n-1)/(get_global_size(0))+1 
      && \gtid + i*get_global_size(0) < n;
        {:zgm[acc1d(\gtid + i*get_global_size(0), z_offset, n, z_inc)]:} ==
       \old(zgm[acc1d(\gtid + i*get_global_size(0), z_offset, n, z_inc)]));
    loop_invariant (\forall int i; 0 <= i && i < id_i
      && \gtid + i*get_global_size(0) < n;
        {:zgm[acc1d(\gtid + i*get_global_size(0), z_offset, n, z_inc)]:} ==
        XhadPure(\old(zgm[acc1d(\gtid + i*get_global_size(0), z_offset, n, z_inc)]), alpha, xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)], beta, 
        ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]));
  @*/
  for (int id = get_global_id(0); id < n; id += get_global_size(0)) {
    int idx = id*x_inc + x_offset;
    int idy = id*y_inc + y_offset;
    int idz = id*z_inc + z_offset;
    /*@
      assert acc1d(id, x_offset, n, x_inc) == idx;
      assert acc1d(id, y_offset, n, y_inc) == idy;
      assert acc1d(id, z_offset, n, z_inc) == idz;
    @*/
    real xvalue = xgm[idx];
    real yvalue = ygm[idy];
    real zvalue = zgm[idz];
    real result;
    real alpha_times_x;
    Multiply(alpha_times_x, alpha, xvalue);
    Multiply(result, alpha_times_x, yvalue);
    MultiplyAdd(result, beta, zvalue);
    zgm[idz] = result;
    //@ assert lemma_mod(id, get_global_size(0));
    //@ ghost id_i++;
  }
}

#ifdef NOT_IGNORE
// Faster version of the kernel without offsets and strided accesses but with if-statement. Also
// assumes that 'n' is dividable by 'VW' and 'WPT'.
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel __attribute__((reqd_work_group_size(WGS, 1, 1)))
#endif
void XhadFaster(const int n, const real_arg arg_alpha, const real_arg arg_beta,
                const __global realV* restrict xgm, const __global realV* restrict ygm,
                __global realV* zgm) {
#if __has_builtin(__builtin_assume)
  __builtin_assume(n % VW == 0);
  __builtin_assume(n % WPT == 0);
#endif
  const real alpha = GetRealArg(arg_alpha);
  const real beta = GetRealArg(arg_beta);

  const int num_desired_threads = n / (VW * WPT);

  if (get_global_id(0) < num_desired_threads) {
    #pragma unroll
    for (int _w = 0; _w < WPT; _w += 1) {
      const int id = _w * num_desired_threads + get_global_id(0);
      realV xvalue = xgm[id];
      realV yvalue = ygm[id];
      realV zvalue = zgm[id];
      realV result;
      realV alpha_times_x;
      alpha_times_x = MultiplyVector(alpha_times_x, alpha, xvalue);
      result = MultiplyVectorVector(result, alpha_times_x, yvalue);
      zgm[id] = MultiplyAddVector(result, beta, zvalue);
    }
  }
}

// Faster version of the kernel without offsets and strided accesses. Also assumes that 'n' is
// dividable by 'VW', 'WGS' and 'WPT'.
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel __attribute__((reqd_work_group_size(WGS, 1, 1)))
#endif
void XhadFastest(const int n, const real_arg arg_alpha, const real_arg arg_beta,
                 const __global realV* restrict xgm, const __global realV* restrict ygm,
                 __global realV* zgm) {
#if __has_builtin(__builtin_assume)
  __builtin_assume(n % VW == 0);
  __builtin_assume(n % WPT == 0);
  __builtin_assume(n % WGS == 0);
#endif
  const real alpha = GetRealArg(arg_alpha);
  const real beta = GetRealArg(arg_beta);

  #pragma unroll
  for (int _w = 0; _w < WPT; _w += 1) {
    const int id = _w*get_global_size(0) + get_global_id(0);
    realV xvalue = xgm[id];
    realV yvalue = ygm[id];
    realV zvalue = zgm[id];
    realV result;
    realV alpha_times_x;
    alpha_times_x = MultiplyVector(alpha_times_x, alpha, xvalue);
    result = MultiplyVectorVector(result, alpha_times_x, yvalue);
    zgm[id] = MultiplyAddVector(result, beta, zvalue);
  }
}
#endif

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
