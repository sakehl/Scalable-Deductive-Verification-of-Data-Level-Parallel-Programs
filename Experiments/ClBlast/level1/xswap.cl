#include "level1.cl"
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains the Xswap kernel. It contains one fast vectorized version in case of unit
// strides (incx=incy=1) and no offsets (offx=offy=0). Another version is more general, but doesn't
// support vector data-types.
//
// This kernel uses the level-1 BLAS common tuning parameters.
//
// =================================================================================================

// Enables loading of this file using the C++ pre-processor's #include (C++11 standard raw string
// literal). Comment-out this line for syntax-highlighting when developing.
//R"(

// =================================================================================================

#ifdef EXTRACT_BODY
/*@ extract_body */
#endif
/*@
  context get_local_size(0) == WGS() && get_local_size(1) == 1 && get_local_size(2) == 1;
  context get_num_groups(0) == 10 && get_num_groups(1) == 1 && get_num_groups(2) == 1;
  context n >= 1;
  context x_inc >= 1 && x_offset >= 0 && xgm != NULL && \pointer_length(xgm) >= n*x_inc+x_offset;
  context y_inc >= 1 && y_offset >= 0 && ygm != NULL && \pointer_length(ygm) >= n*y_inc+y_offset;
  context (\forall* int i; 0 <= i && i < (n-1)/(get_global_size(0))+1
    && \gtid + i*get_global_size(0) < n;
      Perm({:xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)]:}, write));
  context (\forall* int i; 0 <= i && i < (n-1)/(get_global_size(0))+1
    && \gtid + i*get_global_size(0) < n;
      Perm({:ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]:}, write));
  
  ensures (\forall int i; 0 <= i && i < (n-1)/(get_global_size(0))+1 && \gtid + i*get_global_size(0) < n;
        {:xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)]:} ==
        \old(ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]));
  ensures (\forall int i; 0 <= i && i < (n-1)/(get_global_size(0))+1 && \gtid + i*get_global_size(0) < n;
        \old(xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)]) ==
        {:ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]:});
@*/
// Full version of the kernel with offsets and strided accesses
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel //__attribute__((reqd_work_group_size(WGS, 1, 1)))
#endif
void Xswap(const int n,
           UNIQUE1 __global real* xgm, const int x_offset, const int x_inc,
           UNIQUE2 __global real* ygm, const int y_offset, const int y_inc) {

  //@ ghost int id_i = 0;
  /*@ loop_invariant \gtid <= id && id < n + get_global_size(0);
    loop_invariant id == \gtid + id_i * get_global_size(0);
    loop_invariant id % get_global_size(0) == \gtid;
    loop_invariant 0 <= id_i && id_i <= (n-1)/(get_global_size(0))+1;

    loop_invariant (\forall* int i; 0 <= i && i < (n-1)/(get_global_size(0))+1 
      && \gtid + i*get_global_size(0) < n;
        Perm({:xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)]:}, write));
    loop_invariant (\forall* int i; 0 <= i && i < (n-1)/(get_global_size(0))+1 
      && \gtid + i*get_global_size(0) < n;
        Perm({:ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]:}, write));
    loop_invariant (\forall int i; id_i <= i && i < (n-1)/(get_global_size(0))+1 
      && \gtid + i*get_global_size(0) < n;
        {:xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)]:} ==
       \old(xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)]));
    loop_invariant (\forall int i; id_i <= i && i < (n-1)/(get_global_size(0))+1 
      && \gtid + i*get_global_size(0) < n;
        {:ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]:} ==
       \old(ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]));
    loop_invariant (\forall int i; 0 <= i && i < id_i
      && \gtid + i*get_global_size(0) < n;
        {:xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)]:} == 
        \old(ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]));
    loop_invariant (\forall int i; 0 <= i && i < id_i
      && \gtid + i*get_global_size(0) < n;
        {:ygm[acc1d(\gtid + i*get_global_size(0), y_offset, n, y_inc)]:} == 
        \old(xgm[acc1d(\gtid + i*get_global_size(0), x_offset, n, x_inc)]));
  @*/
  // Loops over the work that needs to be done (allows for an arbitrary number of threads)
  for (int id = get_global_id(0); id<n; id += get_global_size(0)) {
    int idx = id*x_inc + x_offset;
    //@ assert acc1d(id, x_offset, n, x_inc) == idx;
    int idy = id*y_inc + y_offset;
    //@ assert acc1d(id, y_offset, n, y_inc) == idy;
    real temp = xgm[idx];
    xgm[idx] = ygm[idy];
    ygm[idy] = temp;
    //@ assert lemma_mod(id, get_global_size(0));
    //@ ghost id_i++;
  }
}

// =================================================================================================

#ifdef NOT_IGNORE
// Faster version of the kernel without offsets and strided accesses. Also assumes that 'n' is
// dividable by 'VW', 'WGS' and 'WPT'.
#if RELAX_WORKGROUP_SIZE == 1
  __kernel
#else
  __kernel __attribute__((reqd_work_group_size(WGS, 1, 1)))
#endif
void XswapFast(const int n,
               __global realV* xgm,
               __global realV* ygm) {
#if __has_builtin(__builtin_assume)
  __builtin_assume(n % VW == 0);
  __builtin_assume(n % WPT == 0);
  __builtin_assume(n % WGS == 0);
#endif
  #pragma unroll
  for (int _w = 0; _w < WPT; _w += 1) {
    const int id = _w*get_global_size(0) + get_global_id(0);
    realV temp = xgm[id];
    xgm[id] = ygm[id];
    ygm[id] = temp;
  }
}
#endif

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
