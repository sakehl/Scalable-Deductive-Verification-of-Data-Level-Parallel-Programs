#include "../common.cl"

real f(int x) {
  return 0.0f;
}
// =================================================================================================
// This file is part of the CLBlast project. Author(s):
//   Cedric Nugteren <www.cedricnugteren.nl>
//
// This file contains common functions for matrix update kernels (Xger, Xher).
//
// =================================================================================================

// Enables loading of this file using the C++ pre-processor's #include (C++11 standard raw string
// literal). Comment-out this line for syntax-highlighting when developing.
//R"(

// =================================================================================================

// Parameters set by the tuner or by the database. Here they are given a basic default value in case
// this kernel file is used outside of the CLBlast library.

// #ifndef WGS1
// //   // The local work-group size in first dimension
// #define WGS1 8    
//   // inline pure int WGS1() = 8;
// #endif
#ifndef WGS2
  // The local work-group size in second dimension
#define WGS2 8    
  //@ inline pure int WGS2() = 8;
#endif
#ifndef WPT
  // The amount of work-per-thread in both dimensions
#define WPT 2     
  //@ inline pure int WPT() = 2;
#endif

// =================================================================================================

/*@
  context gm != NULL && \pointer_length(gm) > offset + (max-1) * inc;
  context 0 <= id && (id < max || id >= max);
  context inc > 0 && offset >= 0;
  context do_conjugate == 0 || do_conjugate == 1;*/
#ifndef CONST_TYPES
//@ requires id < max ==> Perm(gm[acc1d(id, offset, max, inc)], read);
#endif
/*@ ensures id < max ==> \result == gm[acc1d(id, offset, max, inc)];
  ensures id >= max ==> \result == 0;@*/
// Returns an element from a vector
/*@ pure @*/ INLINE_FUNC real LoadVector(const int id, const int max,
                            READ_ONLY0 /*__global*/ real* gm, const int offset, const int inc,
                            const int do_conjugate) {
  if (id < max) {
    int idx = id*inc + offset;
    //@ assert idx == acc1d(id, offset, max, inc);
    // real result = gm[idx];
    real result = gm[acc1d(id, offset, max, inc)];
    if (do_conjugate == 1) {
      #if defined(ROUTINE_GERC) || defined(ROUTINE_HER) || defined(ROUTINE_HPR) || defined(ROUTINE_HER2) || defined(ROUTINE_HPR2)
        COMPLEX_CONJUGATE(result);
      #endif
    }
    return result;
  }
  else {
    SetToZero(real default_result);
    return default_result;
  }
}

/*@
  context max1 > 0 && id1 >= 0;
  context max2 > 0 && id2 >= 0 && 
    a_ld > 0 && a_ld >= max1 && a_offset >= 0;
  context agm != NULL && \pointer_length(agm) >= a_ld * max2 + a_offset;
  context id1 < max1 && id2 < max2 ==> 
    Perm(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)], write);
  ensures id1 < max1 && id2 < max2 ==>
    agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)] ==
      \old(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)]) + alpha * xvalue * yvalue;
  decreases;
@*/
// Performs the rank-1 matrix update
INLINE_FUNC void MatrixUpdate(const int id1, const int id2, const int max1, const int max2,
                              /*__global*/ real* agm, const int a_offset, const int a_ld,
                              const real alpha, const real xvalue, const real yvalue,
                              const int is_upper) {

  // Bounds of a regular matrix
  if (id1 < max1 && id2 < max2) {

    #if defined(ROUTINE_SPR) || defined(ROUTINE_HPR)
      int a_index;
      if (is_upper) {
        a_index = (id1 <= id2) ? ((id2+1)*id2)/2 + id1 : ((id1+1)*id1)/2 + id2;
      }
      else {
        a_index = (id1 >= id2) ? ((2*a_ld-(id2+1))*id2)/2 + id1 : ((2*a_ld-(id1+1))*id1)/2 + id2;
      }
      a_index += a_offset;
    #else
      const int a_index = id2*a_ld + id1 + a_offset;
      //@ assert a_index == acc2d(id1, id2, a_offset, a_ld, max2, a_ld);
    #endif

    // Loads the current value of the A matrix
    const real avalue = agm[a_index];

    // Computes result = alpha * x[i] * y[j] + a[i][j]
    #if PRECISION == 3232 || PRECISION == 6464
      real ax;
      ax.x = MulReal(alpha, xvalue);
      ax.y = MulImag(alpha, xvalue);
      real result;
      result.x = MulReal(ax, yvalue) + avalue.x;
      result.y = MulImag(ax, yvalue) + avalue.y;
    #else
      real result = alpha * xvalue * yvalue + avalue;
    #endif

    // For hermetian matrices
    #if defined(ROUTINE_HER) || defined(ROUTINE_HPR)
      if (id1 == id2) { result.y = ZERO; }
    #endif
    
    // Stores the final result
    agm[a_index] = result;
  }
}


/*@
  context max1 > 0 && id1 >= 0;
  context max2 > 0 && id2 >= 0 &&
    a_ld > 0 && a_ld >= max1 && a_offset >= 0;
  context agm != NULL && \pointer_length(agm) >= a_ld * max2 + a_offset;
  context id1 < max1 && id2 < max2 ==> 
    Perm(agm[acc2d(id1, id2, a_offset, a_ld, max2, a_ld)], write);
  ensures id1 < max1 && id2 < max2 ==>
    agm[acc2d(id1, id2, a_offset, max1, max2, a_ld)] == alpha1 * xvalue * yvalue + alpha2 * xtvalue * ytvalue +
      \old(agm[acc2d(id1, id2, a_offset, max1, max2, a_ld)]);
  decreases;
@*/
// Performs the rank-2 matrix update
/*INLINE_FUNC*/ void MatrixUpdate2(const int id1, const int id2, const int max1, const int max2,
                               /*__global*/ real* agm, const int a_offset, const int a_ld,
                               const real alpha1, const real xvalue, const real yvalue,
                               const real alpha2, const real xtvalue, const real ytvalue,
                               const int is_upper) {
  // Bounds of a regular matrix
  if (id1 < max1 && id2 < max2) {

    #if defined(ROUTINE_SPR2) || defined(ROUTINE_HPR2)
      int a_index;
      if (is_upper) {
        a_index = (id1 <= id2) ? ((id2+1)*id2)/2 + id1 : ((id1+1)*id1)/2 + id2;
      }
      else {
        a_index = (id1 >= id2) ? ((2*a_ld-(id2+1))*id2)/2 + id1 : ((2*a_ld-(id1+1))*id1)/2 + id2;
      }
      a_index += a_offset;
    #else
      const int a_index = id2*a_ld + id1 + a_offset;
    #endif

    // Loads the current value of the A matrix
    const real avalue = agm[a_index];

    // Computes result = alpha * x[i] * y[j] + alpha * x[j] * y[i] + a[i][j]
    #if PRECISION == 3232 || PRECISION == 6464
      real ax;
      ax.x = MulReal(alpha2, xvalue);
      ax.y = MulImag(alpha2, xvalue);
      real atx;
      atx.x = MulReal(alpha1, xtvalue);
      atx.y = MulImag(alpha1, xtvalue);
      real result;
      result.x = MulReal(ax, yvalue) + MulReal(atx, ytvalue) + avalue.x;
      result.y = MulImag(ax, yvalue) + MulImag(atx, ytvalue) + avalue.y;
    #else
      real result = alpha1 * xvalue * yvalue + alpha2 * xtvalue * ytvalue + avalue;
    #endif

    // For hermetian matrices
    #if defined(ROUTINE_HER2) || defined(ROUTINE_HPR2)
      if (id1 == id2) { result.y = ZERO; }
    #endif

    // Stores the final result
    agm[a_index] = result;
  }
}

// =================================================================================================

// End of the C++11 raw string literal
//)"

// =================================================================================================
