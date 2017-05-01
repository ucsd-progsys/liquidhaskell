#include <gsl/gsl_complex.h>

#define RVEC(A) int A##n, double*A##p
#define RMAT(A) int A##r, int A##c, double* A##p
#define KRVEC(A) int A##n, const double*A##p
#define KRMAT(A) int A##r, int A##c, const double* A##p

#define CVEC(A) int A##n, gsl_complex*A##p
#define CMAT(A) int A##r, int A##c, gsl_complex* A##p
#define KCVEC(A) int A##n, const gsl_complex*A##p
#define KCMAT(A) int A##r, int A##c, const gsl_complex* A##p

#define FVEC(A) int A##n, float*A##p
#define FMAT(A) int A##r, int A##c, float* A##p
#define KFVEC(A) int A##n, const float*A##p
#define KFMAT(A) int A##r, int A##c, const float* A##p

#define QVEC(A) int A##n, gsl_complex_float*A##p
#define QMAT(A) int A##r, int A##c, gsl_complex_float* A##p
#define KQVEC(A) int A##n, const gsl_complex_float*A##p
#define KQMAT(A) int A##r, int A##c, const gsl_complex_float* A##p

#include <gsl/gsl_blas.h>
#include <gsl/gsl_math.h>
#include <gsl/gsl_errno.h>
#include <gsl/gsl_fft_complex.h>
#include <gsl/gsl_integration.h>
#include <gsl/gsl_deriv.h>
#include <gsl/gsl_poly.h>
#include <gsl/gsl_multimin.h>
#include <gsl/gsl_multiroots.h>
#include <gsl/gsl_complex_math.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>
#include <gsl/gsl_roots.h>
#include <gsl/gsl_multifit_nlin.h>
#include <string.h>
#include <stdio.h>

#define MACRO(B) do {B} while (0)
#define ERROR(CODE) MACRO(return CODE;)
#define REQUIRES(COND, CODE) MACRO(if(!(COND)) {ERROR(CODE);})
#define OK return 0;

#define MIN(A,B) ((A)<(B)?(A):(B))
#define MAX(A,B) ((A)>(B)?(A):(B))

#ifdef DBG
#define DEBUGMSG(M) printf("*** calling aux C function: %s\n",M);
#else
#define DEBUGMSG(M)
#endif

#define CHECK(RES,CODE) MACRO(if(RES) return CODE;)

#ifdef DBG
#define DEBUGMAT(MSG,X) printf(MSG" = \n"); gsl_matrix_fprintf(stdout,X,"%f"); printf("\n");
#else
#define DEBUGMAT(MSG,X)
#endif

#ifdef DBG
#define DEBUGVEC(MSG,X) printf(MSG" = \n"); gsl_vector_fprintf(stdout,X,"%f"); printf("\n");
#else
#define DEBUGVEC(MSG,X)
#endif

#define DVVIEW(A) gsl_vector_view A = gsl_vector_view_array(A##p,A##n)
#define DMVIEW(A) gsl_matrix_view A = gsl_matrix_view_array(A##p,A##r,A##c)
#define CVVIEW(A) gsl_vector_complex_view A = gsl_vector_complex_view_array((double*)A##p,A##n)
#define CMVIEW(A) gsl_matrix_complex_view A = gsl_matrix_complex_view_array((double*)A##p,A##r,A##c)
#define KDVVIEW(A) gsl_vector_const_view A = gsl_vector_const_view_array(A##p,A##n)
#define KDMVIEW(A) gsl_matrix_const_view A = gsl_matrix_const_view_array(A##p,A##r,A##c)
#define KCVVIEW(A) gsl_vector_complex_const_view A = gsl_vector_complex_const_view_array((double*)A##p,A##n)
#define KCMVIEW(A) gsl_matrix_complex_const_view A = gsl_matrix_complex_const_view_array((double*)A##p,A##r,A##c)

#define FVVIEW(A) gsl_vector_float_view A = gsl_vector_float_view_array(A##p,A##n)
#define FMVIEW(A) gsl_matrix_float_view A = gsl_matrix_float_view_array(A##p,A##r,A##c)
#define QVVIEW(A) gsl_vector_complex_float_view A = gsl_vector_float_complex_view_array((float*)A##p,A##n)
#define QMVIEW(A) gsl_matrix_complex_float_view A = gsl_matrix_float_complex_view_array((float*)A##p,A##r,A##c)
#define KFVVIEW(A) gsl_vector_float_const_view A = gsl_vector_float_const_view_array(A##p,A##n)
#define KFMVIEW(A) gsl_matrix_float_const_view A = gsl_matrix_float_const_view_array(A##p,A##r,A##c)
#define KQVVIEW(A) gsl_vector_complex_float_const_view A = gsl_vector_complex_float_const_view_array((float*)A##p,A##n)
#define KQMVIEW(A) gsl_matrix_complex_float_const_view A = gsl_matrix_complex_float_const_view_array((float*)A##p,A##r,A##c)

#define V(a) (&a.vector)
#define M(a) (&a.matrix)

#define GCVEC(A) int A##n, gsl_complex*A##p
#define KGCVEC(A) int A##n, const gsl_complex*A##p

#define GQVEC(A) int A##n, gsl_complex_float*A##p
#define KGQVEC(A) int A##n, const gsl_complex_float*A##p

#define BAD_SIZE 2000
#define BAD_CODE 2001
#define MEM      2002
#define BAD_FILE 2003


void no_abort_on_error() {
    gsl_set_error_handler_off();
}


int sumF(KFVEC(x),FVEC(r)) {
    DEBUGMSG("sumF");
    REQUIRES(rn==1,BAD_SIZE);
    int i;
    float res = 0;
    for (i = 0; i < xn; i++) res += xp[i];
    rp[0] = res;
    OK
}
    
int sumR(KRVEC(x),RVEC(r)) {
    DEBUGMSG("sumR");
    REQUIRES(rn==1,BAD_SIZE);
    int i;
    double res = 0;
    for (i = 0; i < xn; i++) res += xp[i];
    rp[0] = res;
    OK
}
    
int sumQ(KQVEC(x),QVEC(r)) {
    DEBUGMSG("sumQ");
    REQUIRES(rn==1,BAD_SIZE);
    int i;
    gsl_complex_float res;
    res.dat[0] = 0;
    res.dat[1] = 0;
    for (i = 0; i < xn; i++) {
      res.dat[0] += xp[i].dat[0];
      res.dat[1] += xp[i].dat[1];
    }
    rp[0] = res;
    OK
}
    
int sumC(KCVEC(x),CVEC(r)) {
    DEBUGMSG("sumC");
    REQUIRES(rn==1,BAD_SIZE);
    int i;
    gsl_complex res;
    res.dat[0] = 0;
    res.dat[1] = 0;
    for (i = 0; i < xn; i++)  {
      res.dat[0] += xp[i].dat[0];
      res.dat[1] += xp[i].dat[1];
    }
    rp[0] = res;
    OK
}

int prodF(KFVEC(x),FVEC(r)) {
    DEBUGMSG("prodF");
    REQUIRES(rn==1,BAD_SIZE);
    int i;
    float res = 1;
    for (i = 0; i < xn; i++) res *= xp[i];
    rp[0] = res;
    OK
}
    
int prodR(KRVEC(x),RVEC(r)) {
    DEBUGMSG("prodR");
    REQUIRES(rn==1,BAD_SIZE);
    int i;
    double res = 1;
    for (i = 0; i < xn; i++) res *= xp[i];
    rp[0] = res;
    OK
}
    
int prodQ(KQVEC(x),QVEC(r)) {
    DEBUGMSG("prodQ");
    REQUIRES(rn==1,BAD_SIZE);
    int i;
    gsl_complex_float res;
    float temp;
    res.dat[0] = 1;
    res.dat[1] = 0;
    for (i = 0; i < xn; i++) {
      temp       = res.dat[0] * xp[i].dat[0] - res.dat[1] * xp[i].dat[1];
      res.dat[1] = res.dat[0] * xp[i].dat[1] + res.dat[1] * xp[i].dat[0];
      res.dat[0] = temp;
    }
    rp[0] = res;
    OK
}
    
int prodC(KCVEC(x),CVEC(r)) {
    DEBUGMSG("prodC");
    REQUIRES(rn==1,BAD_SIZE);
    int i;
    gsl_complex res;
    double temp;
    res.dat[0] = 1;
    res.dat[1] = 0;
    for (i = 0; i < xn; i++)  {
      temp       = res.dat[0] * xp[i].dat[0] - res.dat[1] * xp[i].dat[1];
      res.dat[1] = res.dat[0] * xp[i].dat[1] + res.dat[1] * xp[i].dat[0];
      res.dat[0] = temp;
    }
    rp[0] = res;
    OK
}

int dotF(KFVEC(x), KFVEC(y), FVEC(r)) {
    DEBUGMSG("dotF");
    REQUIRES(xn==yn,BAD_SIZE); 
    REQUIRES(rn==1,BAD_SIZE);
    DEBUGMSG("dotF");
    KFVVIEW(x);
    KFVVIEW(y);
    gsl_blas_sdot(V(x),V(y),rp);
    OK
}
    
int dotR(KRVEC(x), KRVEC(y), RVEC(r)) {
    DEBUGMSG("dotR");
    REQUIRES(xn==yn,BAD_SIZE); 
    REQUIRES(rn==1,BAD_SIZE);
    DEBUGMSG("dotR");
    KDVVIEW(x);
    KDVVIEW(y);
    gsl_blas_ddot(V(x),V(y),rp);
    OK
}
    
int dotQ(KQVEC(x), KQVEC(y), QVEC(r)) {
    DEBUGMSG("dotQ");
    REQUIRES(xn==yn,BAD_SIZE); 
    REQUIRES(rn==1,BAD_SIZE);
    DEBUGMSG("dotQ");
    KQVVIEW(x);
    KQVVIEW(y);
    gsl_blas_cdotu(V(x),V(y),rp);
    OK
}
    
int dotC(KCVEC(x), KCVEC(y), CVEC(r)) {
    DEBUGMSG("dotC");
    REQUIRES(xn==yn,BAD_SIZE); 
    REQUIRES(rn==1,BAD_SIZE);
    DEBUGMSG("dotC");
    KCVVIEW(x);
    KCVVIEW(y);
    gsl_blas_zdotu(V(x),V(y),rp);
    OK
}
    
int toScalarR(int code, KRVEC(x), RVEC(r)) { 
    REQUIRES(rn==1,BAD_SIZE);
    DEBUGMSG("toScalarR");
    KDVVIEW(x);
    double res;
    switch(code) {
        case 0: { res = gsl_blas_dnrm2(V(x)); break; } 
        case 1: { res = gsl_blas_dasum(V(x));  break; }
        case 2: { res = gsl_vector_max_index(V(x));  break; }
        case 3: { res = gsl_vector_max(V(x));  break; }
        case 4: { res = gsl_vector_min_index(V(x)); break; }
        case 5: { res = gsl_vector_min(V(x)); break; }
        default: ERROR(BAD_CODE);
    }
    rp[0] = res;
    OK
}

int toScalarF(int code, KFVEC(x), FVEC(r)) { 
    REQUIRES(rn==1,BAD_SIZE);
    DEBUGMSG("toScalarF");
    KFVVIEW(x);
    float res;
    switch(code) {
        case 0: { res = gsl_blas_snrm2(V(x)); break; } 
        case 1: { res = gsl_blas_sasum(V(x));  break; }
        case 2: { res = gsl_vector_float_max_index(V(x));  break; }
        case 3: { res = gsl_vector_float_max(V(x));  break; }
        case 4: { res = gsl_vector_float_min_index(V(x)); break; }
        case 5: { res = gsl_vector_float_min(V(x)); break; }
        default: ERROR(BAD_CODE);
    }
    rp[0] = res;
    OK
}


int toScalarC(int code, KCVEC(x), RVEC(r)) { 
    REQUIRES(rn==1,BAD_SIZE);
    DEBUGMSG("toScalarC");
    KCVVIEW(x);
    double res;
    switch(code) {
        case 0: { res = gsl_blas_dznrm2(V(x)); break; } 
        case 1: { res = gsl_blas_dzasum(V(x));  break; }
        default: ERROR(BAD_CODE);
    }
    rp[0] = res;
    OK
}

int toScalarQ(int code, KQVEC(x), FVEC(r)) { 
    REQUIRES(rn==1,BAD_SIZE);
    DEBUGMSG("toScalarQ");
    KQVVIEW(x);
    float res;
    switch(code) {
        case 0: { res = gsl_blas_scnrm2(V(x)); break; } 
        case 1: { res = gsl_blas_scasum(V(x));  break; }
        default: ERROR(BAD_CODE);
    }
    rp[0] = res;
    OK
}


inline double sign(double x) {
    if(x>0) {
        return +1.0;
    } else if (x<0) {
        return -1.0;
    } else {
        return 0.0;
    }
}

inline float float_sign(float x) {
    if(x>0) {
        return +1.0;
    } else if (x<0) {
        return -1.0;
    } else {
        return 0.0;
    }
}

inline gsl_complex complex_abs(gsl_complex z) {
    gsl_complex r;
    r.dat[0] = gsl_complex_abs(z);
    r.dat[1] = 0;
    return r;
}

inline gsl_complex complex_signum(gsl_complex z) {
    gsl_complex r;
    double mag;
    if (z.dat[0] == 0 && z.dat[1] == 0) {
        r.dat[0] = 0;
        r.dat[1] = 0;
    } else {
        mag = gsl_complex_abs(z);
        r.dat[0] = z.dat[0]/mag;
        r.dat[1] = z.dat[1]/mag;
    }
    return r;
}

#define OP(C,F) case C: { for(k=0;k<xn;k++) rp[k] = F(xp[k]); OK }
#define OPV(C,E) case C: { for(k=0;k<xn;k++) rp[k] = E; OK }
int mapR(int code, KRVEC(x), RVEC(r)) {
    int k;
    REQUIRES(xn == rn,BAD_SIZE);
    DEBUGMSG("mapR");
    switch (code) {
        OP(0,sin)
        OP(1,cos)
        OP(2,tan)
        OP(3,fabs)
        OP(4,asin)
        OP(5,acos)
        OP(6,atan) /* atan2 mediante vectorZip */
        OP(7,sinh)
        OP(8,cosh)
        OP(9,tanh)
        OP(10,gsl_asinh)
        OP(11,gsl_acosh)
        OP(12,gsl_atanh)
        OP(13,exp)
        OP(14,log)
        OP(15,sign)
        OP(16,sqrt)
        default: ERROR(BAD_CODE);
    }
}

int mapF(int code, KFVEC(x), FVEC(r)) {
    int k;
    REQUIRES(xn == rn,BAD_SIZE);
    DEBUGMSG("mapF");
    switch (code) {
        OP(0,sin)
        OP(1,cos)
        OP(2,tan)
        OP(3,fabs)
        OP(4,asin)
        OP(5,acos)
        OP(6,atan) /* atan2 mediante vectorZip */
        OP(7,sinh)
        OP(8,cosh)
        OP(9,tanh)
        OP(10,gsl_asinh)
        OP(11,gsl_acosh)
        OP(12,gsl_atanh)
        OP(13,exp)
        OP(14,log)
        OP(15,sign)
        OP(16,sqrt)
        default: ERROR(BAD_CODE);
    }
}


int mapCAux(int code, KGCVEC(x), GCVEC(r)) {
    int k;
    REQUIRES(xn == rn,BAD_SIZE);
    DEBUGMSG("mapC");
    switch (code) {
        OP(0,gsl_complex_sin)
        OP(1,gsl_complex_cos)
        OP(2,gsl_complex_tan)
        OP(3,complex_abs)
        OP(4,gsl_complex_arcsin)
        OP(5,gsl_complex_arccos)
        OP(6,gsl_complex_arctan)
        OP(7,gsl_complex_sinh)
        OP(8,gsl_complex_cosh)
        OP(9,gsl_complex_tanh)
        OP(10,gsl_complex_arcsinh)
        OP(11,gsl_complex_arccosh)
        OP(12,gsl_complex_arctanh)
        OP(13,gsl_complex_exp)
        OP(14,gsl_complex_log)
        OP(15,complex_signum)
        OP(16,gsl_complex_sqrt)

        // gsl_complex_arg
        // gsl_complex_abs
        default: ERROR(BAD_CODE);
    }
}

int mapC(int code, KCVEC(x), CVEC(r)) {
    return mapCAux(code, xn, (gsl_complex*)xp, rn, (gsl_complex*)rp);
}


gsl_complex_float complex_float_math_fun(gsl_complex (*cf)(gsl_complex), gsl_complex_float a)
{
  gsl_complex c;
  gsl_complex r;

  gsl_complex_float float_r;

  c.dat[0] = a.dat[0];
  c.dat[1] = a.dat[1];

  r = (*cf)(c);

  float_r.dat[0] = r.dat[0];
  float_r.dat[1] = r.dat[1];

  return float_r;
}

gsl_complex_float complex_float_math_op(gsl_complex (*cf)(gsl_complex,gsl_complex), 
					gsl_complex_float a,gsl_complex_float b)
{
  gsl_complex c1;
  gsl_complex c2;
  gsl_complex r;

  gsl_complex_float float_r;

  c1.dat[0] = a.dat[0];
  c1.dat[1] = a.dat[1];

  c2.dat[0] = b.dat[0];
  c2.dat[1] = b.dat[1];

  r = (*cf)(c1,c2);

  float_r.dat[0] = r.dat[0];
  float_r.dat[1] = r.dat[1];

  return float_r;
}

#define OPC(C,F) case C: { for(k=0;k<xn;k++) rp[k] = complex_float_math_fun(&F,xp[k]); OK }
#define OPCA(C,F,A,B) case C: { for(k=0;k<xn;k++) rp[k] = complex_float_math_op(&F,A,B); OK }
int mapQAux(int code, KGQVEC(x), GQVEC(r)) {
    int k;
    REQUIRES(xn == rn,BAD_SIZE);
    DEBUGMSG("mapQ");
    switch (code) {
        OPC(0,gsl_complex_sin)
        OPC(1,gsl_complex_cos)
        OPC(2,gsl_complex_tan)
        OPC(3,complex_abs)
        OPC(4,gsl_complex_arcsin)
        OPC(5,gsl_complex_arccos)
        OPC(6,gsl_complex_arctan)
        OPC(7,gsl_complex_sinh)
        OPC(8,gsl_complex_cosh)
        OPC(9,gsl_complex_tanh)
        OPC(10,gsl_complex_arcsinh)
        OPC(11,gsl_complex_arccosh)
        OPC(12,gsl_complex_arctanh)
        OPC(13,gsl_complex_exp)
        OPC(14,gsl_complex_log)
        OPC(15,complex_signum)
        OPC(16,gsl_complex_sqrt)

        // gsl_complex_arg
        // gsl_complex_abs
        default: ERROR(BAD_CODE);
    }
}

int mapQ(int code, KQVEC(x), QVEC(r)) {
    return mapQAux(code, xn, (gsl_complex_float*)xp, rn, (gsl_complex_float*)rp);
}


int mapValR(int code, double* pval, KRVEC(x), RVEC(r)) {
    int k;
    double val = *pval;
    REQUIRES(xn == rn,BAD_SIZE);
    DEBUGMSG("mapValR");
    switch (code) {
        OPV(0,val*xp[k])
        OPV(1,val/xp[k])
        OPV(2,val+xp[k])
        OPV(3,val-xp[k])
        OPV(4,pow(val,xp[k]))
        OPV(5,pow(xp[k],val))
        default: ERROR(BAD_CODE);
    }
}

int mapValF(int code, float* pval, KFVEC(x), FVEC(r)) {
    int k;
    float val = *pval;
    REQUIRES(xn == rn,BAD_SIZE);
    DEBUGMSG("mapValF");
    switch (code) {
        OPV(0,val*xp[k])
        OPV(1,val/xp[k])
        OPV(2,val+xp[k])
        OPV(3,val-xp[k])
        OPV(4,pow(val,xp[k]))
        OPV(5,pow(xp[k],val))
        default: ERROR(BAD_CODE);
    }
}

int mapValCAux(int code, gsl_complex* pval, KGCVEC(x), GCVEC(r)) {
    int k;
    gsl_complex val = *pval;
    REQUIRES(xn == rn,BAD_SIZE);
    DEBUGMSG("mapValC");
    switch (code) {
        OPV(0,gsl_complex_mul(val,xp[k]))
        OPV(1,gsl_complex_div(val,xp[k]))
        OPV(2,gsl_complex_add(val,xp[k]))
        OPV(3,gsl_complex_sub(val,xp[k]))
        OPV(4,gsl_complex_pow(val,xp[k]))
        OPV(5,gsl_complex_pow(xp[k],val))
        default: ERROR(BAD_CODE);
    }
}

int mapValC(int code, gsl_complex* val, KCVEC(x), CVEC(r)) {
    return mapValCAux(code, val, xn, (gsl_complex*)xp, rn, (gsl_complex*)rp);
}


int mapValQAux(int code, gsl_complex_float* pval, KQVEC(x), GQVEC(r)) {
    int k;
    gsl_complex_float val = *pval;
    REQUIRES(xn == rn,BAD_SIZE);
    DEBUGMSG("mapValQ");
    switch (code) {
        OPCA(0,gsl_complex_mul,val,xp[k])
	OPCA(1,gsl_complex_div,val,xp[k])
	OPCA(2,gsl_complex_add,val,xp[k])
	OPCA(3,gsl_complex_sub,val,xp[k])
	OPCA(4,gsl_complex_pow,val,xp[k])
	OPCA(5,gsl_complex_pow,xp[k],val)
        default: ERROR(BAD_CODE);
    }
}

int mapValQ(int code, gsl_complex_float* val, KQVEC(x), QVEC(r)) {
    return mapValQAux(code, val, xn, (gsl_complex_float*)xp, rn, (gsl_complex_float*)rp);
}


#define OPZE(C,msg,E) case C: {DEBUGMSG(msg) for(k=0;k<an;k++) rp[k] = E(ap[k],bp[k]); OK }
#define OPZV(C,msg,E) case C: {DEBUGMSG(msg) res = E(V(r),V(b)); CHECK(res,res); OK }
int zipR(int code, KRVEC(a), KRVEC(b), RVEC(r)) {
    REQUIRES(an == bn && an == rn, BAD_SIZE);
    int k;
    switch(code) {
        OPZE(4,"zipR Pow",pow)
        OPZE(5,"zipR ATan2",atan2)
    }
    KDVVIEW(a);
    KDVVIEW(b);
    DVVIEW(r);
    gsl_vector_memcpy(V(r),V(a));
    int res;
    switch(code) {
        OPZV(0,"zipR Add",gsl_vector_add)
        OPZV(1,"zipR Sub",gsl_vector_sub)
        OPZV(2,"zipR Mul",gsl_vector_mul)
        OPZV(3,"zipR Div",gsl_vector_div)
        default: ERROR(BAD_CODE);
    }
}


int zipF(int code, KFVEC(a), KFVEC(b), FVEC(r)) {
    REQUIRES(an == bn && an == rn, BAD_SIZE);
    int k;
    switch(code) {
        OPZE(4,"zipF Pow",pow)
        OPZE(5,"zipF ATan2",atan2)
    }
    KFVVIEW(a);
    KFVVIEW(b);
    FVVIEW(r);
    gsl_vector_float_memcpy(V(r),V(a));
    int res;
    switch(code) {
        OPZV(0,"zipF Add",gsl_vector_float_add)
        OPZV(1,"zipF Sub",gsl_vector_float_sub)
        OPZV(2,"zipF Mul",gsl_vector_float_mul)
        OPZV(3,"zipF Div",gsl_vector_float_div)
        default: ERROR(BAD_CODE);
    }
}


int zipCAux(int code, KGCVEC(a), KGCVEC(b), GCVEC(r)) {
    REQUIRES(an == bn && an == rn, BAD_SIZE);
    int k;
    switch(code) {
        OPZE(0,"zipC Add",gsl_complex_add)
        OPZE(1,"zipC Sub",gsl_complex_sub)
        OPZE(2,"zipC Mul",gsl_complex_mul)
        OPZE(3,"zipC Div",gsl_complex_div)
        OPZE(4,"zipC Pow",gsl_complex_pow)
        //OPZE(5,"zipR ATan2",atan2)
    }
    //KCVVIEW(a);
    //KCVVIEW(b);
    //CVVIEW(r);
    //gsl_vector_memcpy(V(r),V(a));
    //int res;
    switch(code) {
        default: ERROR(BAD_CODE);
    }
}


int zipC(int code, KCVEC(a), KCVEC(b), CVEC(r)) {
    return zipCAux(code, an, (gsl_complex*)ap, bn, (gsl_complex*)bp, rn, (gsl_complex*)rp);
}


#define OPCZE(C,msg,E) case C: {DEBUGMSG(msg) for(k=0;k<an;k++) rp[k] = complex_float_math_op(&E,ap[k],bp[k]); OK }
int zipQAux(int code, KGQVEC(a), KGQVEC(b), GQVEC(r)) {
    REQUIRES(an == bn && an == rn, BAD_SIZE);
    int k;
    switch(code) {
        OPCZE(0,"zipQ Add",gsl_complex_add)
        OPCZE(1,"zipQ Sub",gsl_complex_sub)
        OPCZE(2,"zipQ Mul",gsl_complex_mul)
        OPCZE(3,"zipQ Div",gsl_complex_div)
        OPCZE(4,"zipQ Pow",gsl_complex_pow)
        //OPZE(5,"zipR ATan2",atan2)
    }
    //KCVVIEW(a);
    //KCVVIEW(b);
    //CVVIEW(r);
    //gsl_vector_memcpy(V(r),V(a));
    //int res;
    switch(code) {
        default: ERROR(BAD_CODE);
    }
}


int zipQ(int code, KQVEC(a), KQVEC(b), QVEC(r)) {
    return zipQAux(code, an, (gsl_complex_float*)ap, bn, (gsl_complex_float*)bp, rn, (gsl_complex_float*)rp);
}



int fft(int code, KCVEC(X), CVEC(R)) {
    REQUIRES(Xn == Rn,BAD_SIZE);
    DEBUGMSG("fft");
    int s = Xn;
    gsl_fft_complex_wavetable * wavetable = gsl_fft_complex_wavetable_alloc (s);
    gsl_fft_complex_workspace * workspace = gsl_fft_complex_workspace_alloc (s);
    gsl_vector_const_view X = gsl_vector_const_view_array((double*)Xp, 2*Xn);
    gsl_vector_view R = gsl_vector_view_array((double*)Rp, 2*Rn);
    gsl_blas_dcopy(&X.vector,&R.vector);
    if(code==0) {
        gsl_fft_complex_forward ((double*)Rp, 1, s, wavetable, workspace);
    } else {
        gsl_fft_complex_inverse ((double*)Rp, 1, s, wavetable, workspace);
    }
    gsl_fft_complex_wavetable_free (wavetable);
    gsl_fft_complex_workspace_free (workspace);
    OK
}


int deriv(int code, double f(double, void*), double x, double h, double * result, double * abserr)
{
    gsl_function F;
    F.function = f;
    F.params = 0;

    if(code==0) return gsl_deriv_central (&F, x, h, result, abserr);

    if(code==1) return gsl_deriv_forward (&F, x, h, result, abserr);

    if(code==2) return gsl_deriv_backward (&F, x, h, result, abserr);

    return 0;
}


int integrate_qng(double f(double, void*), double a, double b, double prec,
                   double *result, double*error) {
    DEBUGMSG("integrate_qng");
    gsl_function F;
    F.function = f;
    F.params = NULL;
    size_t neval;
    int res = gsl_integration_qng (&F, a,b, 0, prec, result, error, &neval); 
    CHECK(res,res);
    OK
}

int integrate_qags(double f(double,void*), double a, double b, double prec, int w, 
               double *result, double* error) {
    DEBUGMSG("integrate_qags");
    gsl_integration_workspace * wk = gsl_integration_workspace_alloc (w);
    gsl_function F;
    F.function = f;
    F.params = NULL;
    int res = gsl_integration_qags (&F, a,b, 0, prec, w,wk, result, error); 
    CHECK(res,res);
    gsl_integration_workspace_free (wk); 
    OK
}

int integrate_qagi(double f(double,void*), double prec, int w, 
               double *result, double* error) {
    DEBUGMSG("integrate_qagi");
    gsl_integration_workspace * wk = gsl_integration_workspace_alloc (w);
    gsl_function F;
    F.function = f;
    F.params = NULL;
    int res = gsl_integration_qagi (&F, 0, prec, w,wk, result, error); 
    CHECK(res,res);
    gsl_integration_workspace_free (wk); 
    OK
}


int integrate_qagiu(double f(double,void*), double a, double prec, int w, 
               double *result, double* error) {
    DEBUGMSG("integrate_qagiu");
    gsl_integration_workspace * wk = gsl_integration_workspace_alloc (w);
    gsl_function F;
    F.function = f;
    F.params = NULL;
    int res = gsl_integration_qagiu (&F, a, 0, prec, w,wk, result, error); 
    CHECK(res,res);
    gsl_integration_workspace_free (wk); 
    OK
}


int integrate_qagil(double f(double,void*), double b, double prec, int w, 
               double *result, double* error) {
    DEBUGMSG("integrate_qagil");
    gsl_integration_workspace * wk = gsl_integration_workspace_alloc (w);
    gsl_function F;
    F.function = f;
    F.params = NULL;
    int res = gsl_integration_qagil (&F, b, 0, prec, w,wk, result, error); 
    CHECK(res,res);
    gsl_integration_workspace_free (wk); 
    OK
}


int polySolve(KRVEC(a), CVEC(z)) {
    DEBUGMSG("polySolve");
    REQUIRES(an>1,BAD_SIZE);
    gsl_poly_complex_workspace * w = gsl_poly_complex_workspace_alloc (an);
    int res = gsl_poly_complex_solve ((double*)ap, an, w, (double*)zp);
    CHECK(res,res);
    gsl_poly_complex_workspace_free (w);
    OK;
}

int vector_fscanf(char*filename, RVEC(a)) {
    DEBUGMSG("gsl_vector_fscanf");
    DVVIEW(a);
    FILE * f = fopen(filename,"r");
    CHECK(!f,BAD_FILE);
    int res = gsl_vector_fscanf(f,V(a));
    CHECK(res,res);
    fclose (f);
    OK
}

int vector_fprintf(char*filename, char*fmt, RVEC(a)) {
    DEBUGMSG("gsl_vector_fprintf");
    DVVIEW(a);
    FILE * f = fopen(filename,"w");
    CHECK(!f,BAD_FILE);
    int res = gsl_vector_fprintf(f,V(a),fmt);
    CHECK(res,res);
    fclose (f);
    OK
}

int vector_fread(char*filename, RVEC(a)) {
    DEBUGMSG("gsl_vector_fread");
    DVVIEW(a);
    FILE * f = fopen(filename,"r");
    CHECK(!f,BAD_FILE);
    int res = gsl_vector_fread(f,V(a));
    CHECK(res,res);
    fclose (f);
    OK
}

int vector_fwrite(char*filename, RVEC(a)) {
    DEBUGMSG("gsl_vector_fwrite");
    DVVIEW(a);
    FILE * f = fopen(filename,"w");
    CHECK(!f,BAD_FILE);
    int res = gsl_vector_fwrite(f,V(a));
    CHECK(res,res);
    fclose (f);
    OK
}

int matrix_fprintf(char*filename, char*fmt, int ro, RMAT(m)) {
    DEBUGMSG("matrix_fprintf");
    FILE * f = fopen(filename,"w");
    CHECK(!f,BAD_FILE);
    int i,j,sr,sc;
    if (ro==1) { sr = mc; sc = 1;} else { sr = 1; sc = mr;}
    #define AT(M,r,c) (M##p[(r)*sr+(c)*sc])
    for (i=0; i<mr; i++) {
        for (j=0; j<mc-1; j++) {
            fprintf(f,fmt,AT(m,i,j));
            fprintf(f," ");
        }
        fprintf(f,fmt,AT(m,i,j));
        fprintf(f,"\n");
    }
    fclose (f);
    OK
}

//---------------------------------------------------------------

typedef double Trawfun(int, double*);

double only_f_aux_min(const gsl_vector*x, void *pars) {
    Trawfun * f = (Trawfun*) pars;  
    double* p = (double*)calloc(x->size,sizeof(double));
    int k;
    for(k=0;k<x->size;k++) {
        p[k] = gsl_vector_get(x,k);
    }  
    double res = f(x->size,p);
    free(p);
    return res;
}

// this version returns info about intermediate steps
int minimize(int method, double f(int, double*), double tolsize, int maxit, 
                 KRVEC(xi), KRVEC(sz), RMAT(sol)) {
    REQUIRES(xin==szn && solr == maxit && solc == 3+xin,BAD_SIZE);
    DEBUGMSG("minimizeList (nmsimplex)");
    gsl_multimin_function my_func;
    // extract function from pars
    my_func.f = only_f_aux_min;
    my_func.n = xin; 
    my_func.params = f;
    size_t iter = 0;
    int status;
    double size;
    const gsl_multimin_fminimizer_type *T;
    gsl_multimin_fminimizer *s = NULL;
    // Initial vertex size vector 
    KDVVIEW(sz);
    // Starting point
    KDVVIEW(xi);
    // Minimizer nmsimplex, without derivatives
    switch(method) {
        case 0 : {T = gsl_multimin_fminimizer_nmsimplex; break; }
#ifdef GSL110
        case 1 : {T = gsl_multimin_fminimizer_nmsimplex; break; }
#else
        case 1 : {T = gsl_multimin_fminimizer_nmsimplex2; break; }
#endif
        default: ERROR(BAD_CODE);
    }
    s = gsl_multimin_fminimizer_alloc (T, my_func.n);
    gsl_multimin_fminimizer_set (s, &my_func, V(xi), V(sz));
    do {
        status = gsl_multimin_fminimizer_iterate (s);
        size = gsl_multimin_fminimizer_size (s);

        solp[iter*solc+0] = iter+1;
        solp[iter*solc+1] = s->fval;
        solp[iter*solc+2] = size;

        int k;
        for(k=0;k<xin;k++) {
            solp[iter*solc+k+3] = gsl_vector_get(s->x,k);
        }
        iter++;
        if (status) break;
        status = gsl_multimin_test_size (size, tolsize);
    } while (status == GSL_CONTINUE && iter < maxit);
    int i,j;
    for (i=iter; i<solr; i++) {
        solp[i*solc+0] = iter;
        for(j=1;j<solc;j++) {
            solp[i*solc+j]=0.;
        }
    }
    gsl_multimin_fminimizer_free(s);
    OK
}

// working with the gradient

typedef struct {double (*f)(int, double*); int (*df)(int, double*, int, double*);} Tfdf;

double f_aux_min(const gsl_vector*x, void *pars) {
    Tfdf * fdf = ((Tfdf*) pars);
    double* p = (double*)calloc(x->size,sizeof(double));
    int k;
    for(k=0;k<x->size;k++) {
        p[k] = gsl_vector_get(x,k);
    }
    double res = fdf->f(x->size,p);
    free(p);
    return res;
}


void df_aux_min(const gsl_vector * x, void * pars, gsl_vector * g) {
    Tfdf * fdf = ((Tfdf*) pars);
    double* p = (double*)calloc(x->size,sizeof(double));
    double* q = (double*)calloc(g->size,sizeof(double));
    int k;
    for(k=0;k<x->size;k++) {
        p[k] = gsl_vector_get(x,k);
    }

    fdf->df(x->size,p,g->size,q);

    for(k=0;k<x->size;k++) {
        gsl_vector_set(g,k,q[k]);
    }
    free(p);
    free(q);
}

void fdf_aux_min(const gsl_vector * x, void * pars, double * f, gsl_vector * g) {
    *f = f_aux_min(x,pars);
    df_aux_min(x,pars,g);
}


int minimizeD(int method, double f(int, double*), int df(int, double*, int, double*),
              double initstep, double minimpar, double tolgrad, int maxit, 
              KRVEC(xi), RMAT(sol)) {
    REQUIRES(solr == maxit && solc == 2+xin,BAD_SIZE);
    DEBUGMSG("minimizeWithDeriv (conjugate_fr)");
    gsl_multimin_function_fdf my_func;
    // extract function from pars
    my_func.f = f_aux_min;
    my_func.df = df_aux_min;
    my_func.fdf = fdf_aux_min;
    my_func.n = xin; 
    Tfdf stfdf;
    stfdf.f = f;
    stfdf.df = df;
    my_func.params = &stfdf;
    size_t iter = 0;
    int status;
    const gsl_multimin_fdfminimizer_type *T;
    gsl_multimin_fdfminimizer *s = NULL;
    // Starting point
    KDVVIEW(xi);
    // conjugate gradient fr
    switch(method) {
        case 0 : {T = gsl_multimin_fdfminimizer_conjugate_fr; break; }
        case 1 : {T = gsl_multimin_fdfminimizer_conjugate_pr; break; }
        case 2 : {T = gsl_multimin_fdfminimizer_vector_bfgs; break; }
        case 3 : {T = gsl_multimin_fdfminimizer_vector_bfgs2; break; }
        case 4 : {T = gsl_multimin_fdfminimizer_steepest_descent; break; }
        default: ERROR(BAD_CODE);
    }
    s = gsl_multimin_fdfminimizer_alloc (T, my_func.n);
    gsl_multimin_fdfminimizer_set (s, &my_func, V(xi), initstep, minimpar);
    do {
        status = gsl_multimin_fdfminimizer_iterate (s);
        solp[iter*solc+0] = iter+1;
        solp[iter*solc+1] = s->f;
        int k;
        for(k=0;k<xin;k++) {
            solp[iter*solc+k+2] = gsl_vector_get(s->x,k);
        }
        iter++;
        if (status) break;
        status = gsl_multimin_test_gradient (s->gradient, tolgrad);
    } while (status == GSL_CONTINUE && iter < maxit);
    int i,j;
    for (i=iter; i<solr; i++) {
        solp[i*solc+0] = iter;
        for(j=1;j<solc;j++) {
            solp[i*solc+j]=0.;
        }
    }
    gsl_multimin_fdfminimizer_free(s);
    OK
}

//---------------------------------------------------------------

double only_f_aux_root(double x, void *pars) {
    double (*f)(double) = (double (*)(double)) pars;
    return f(x);
}

int root(int method, double f(double),
         double epsrel, int maxit,
         double xl, double xu, RMAT(sol)) {
    REQUIRES(solr == maxit && solc == 4,BAD_SIZE);
    DEBUGMSG("root_only_f");
    gsl_function my_func;
    // extract function from pars
    my_func.function = only_f_aux_root;
    my_func.params = f;
    size_t iter = 0;
    int status;
    const gsl_root_fsolver_type *T;
    gsl_root_fsolver *s;
    // Starting point
    switch(method) {
        case 0 : {T = gsl_root_fsolver_bisection; printf("7\n"); break; }
        case 1 : {T = gsl_root_fsolver_falsepos; break; }
        case 2 : {T = gsl_root_fsolver_brent; break; }
        default: ERROR(BAD_CODE);
    }
    s = gsl_root_fsolver_alloc (T);
    gsl_root_fsolver_set (s, &my_func, xl, xu);
    do {
           double best, current_lo, current_hi;
           status = gsl_root_fsolver_iterate (s);
           best = gsl_root_fsolver_root (s);
           current_lo = gsl_root_fsolver_x_lower (s);
           current_hi = gsl_root_fsolver_x_upper (s);
           solp[iter*solc] = iter + 1;
           solp[iter*solc+1] = best;
           solp[iter*solc+2] = current_lo;
           solp[iter*solc+3] = current_hi;
           iter++;
           if (status)   /* check if solver is stuck */
             break;

           status =
               gsl_root_test_interval (current_lo, current_hi, 0, epsrel);
        }
        while (status == GSL_CONTINUE && iter < maxit);
    int i;
    for (i=iter; i<solr; i++) {
        solp[i*solc+0] = iter;
        solp[i*solc+1]=0.;
        solp[i*solc+2]=0.;
        solp[i*solc+3]=0.;
    }
    gsl_root_fsolver_free(s);
    OK
}

typedef struct {
    double (*f)(double);
    double (*jf)(double);
} uniTfjf;

double f_aux_uni(double x, void *pars) {
    uniTfjf * fjf = ((uniTfjf*) pars);
    return (fjf->f)(x);
}

double jf_aux_uni(double x, void * pars) {
    uniTfjf * fjf = ((uniTfjf*) pars);
    return (fjf->jf)(x);
}

void fjf_aux_uni(double x, void * pars, double * f, double * g) {
    *f = f_aux_uni(x,pars);
    *g = jf_aux_uni(x,pars);
}

int rootj(int method, double f(double),
          double df(double),
         double epsrel, int maxit,
         double x, RMAT(sol)) {
    REQUIRES(solr == maxit && solc == 2,BAD_SIZE);
    DEBUGMSG("root_fjf");
    gsl_function_fdf my_func;
    // extract function from pars
    my_func.f = f_aux_uni;
    my_func.df = jf_aux_uni;
    my_func.fdf = fjf_aux_uni;
    uniTfjf stfjf;
    stfjf.f = f;
    stfjf.jf = df;
    my_func.params = &stfjf;
    size_t iter = 0;
    int status;
    const gsl_root_fdfsolver_type *T;
    gsl_root_fdfsolver *s;
    // Starting point
    switch(method) {
        case 0 : {T = gsl_root_fdfsolver_newton;; break; }
        case 1 : {T = gsl_root_fdfsolver_secant; break; }
        case 2 : {T = gsl_root_fdfsolver_steffenson; break; }
        default: ERROR(BAD_CODE);
    }
    s = gsl_root_fdfsolver_alloc (T);

    gsl_root_fdfsolver_set (s, &my_func, x);

    do {
           double x0;
           status = gsl_root_fdfsolver_iterate (s);
           x0 = x;
           x = gsl_root_fdfsolver_root(s);
           solp[iter*solc+0] = iter+1;
           solp[iter*solc+1] = x;

           iter++;
           if (status)   /* check if solver is stuck */
             break;

           status =
               gsl_root_test_delta (x, x0, 0, epsrel);
        }
        while (status == GSL_CONTINUE && iter < maxit);

    int i;
    for (i=iter; i<solr; i++) {
        solp[i*solc+0] = iter;
        solp[i*solc+1]=0.;
    }
    gsl_root_fdfsolver_free(s);
    OK
}


//---------------------------------------------------------------

typedef void TrawfunV(int, double*, int, double*);

int only_f_aux_multiroot(const gsl_vector*x, void *pars, gsl_vector*y) {
    TrawfunV * f = (TrawfunV*) pars;
    double* p = (double*)calloc(x->size,sizeof(double));
    double* q = (double*)calloc(y->size,sizeof(double));
    int k;
    for(k=0;k<x->size;k++) {
        p[k] = gsl_vector_get(x,k);
    }
    f(x->size,p,y->size,q);
    for(k=0;k<y->size;k++) {
        gsl_vector_set(y,k,q[k]);
    }
    free(p);
    free(q);
    return 0; //hmmm
}

int multiroot(int method, void f(int, double*, int, double*),
         double epsabs, int maxit,
         KRVEC(xi), RMAT(sol)) {
    REQUIRES(solr == maxit && solc == 1+2*xin,BAD_SIZE);
    DEBUGMSG("root_only_f");
    gsl_multiroot_function my_func;
    // extract function from pars
    my_func.f = only_f_aux_multiroot;
    my_func.n = xin;
    my_func.params = f;
    size_t iter = 0;
    int status;
    const gsl_multiroot_fsolver_type *T;
    gsl_multiroot_fsolver *s;
    // Starting point
    KDVVIEW(xi);
    switch(method) {
        case 0 : {T = gsl_multiroot_fsolver_hybrids;; break; }
        case 1 : {T = gsl_multiroot_fsolver_hybrid; break; }
        case 2 : {T = gsl_multiroot_fsolver_dnewton; break; }
        case 3 : {T = gsl_multiroot_fsolver_broyden; break; }
        default: ERROR(BAD_CODE);
    }
    s = gsl_multiroot_fsolver_alloc (T, my_func.n);
    gsl_multiroot_fsolver_set (s, &my_func, V(xi));

    do {
           status = gsl_multiroot_fsolver_iterate (s);

           solp[iter*solc+0] = iter+1;

           int k;
           for(k=0;k<xin;k++) {
               solp[iter*solc+k+1] = gsl_vector_get(s->x,k);
           }
           for(k=xin;k<2*xin;k++) {
               solp[iter*solc+k+1] = gsl_vector_get(s->f,k-xin);
           }

           iter++;
           if (status)   /* check if solver is stuck */
             break;

           status =
             gsl_multiroot_test_residual (s->f, epsabs);
        }
        while (status == GSL_CONTINUE && iter < maxit);

    int i,j;
    for (i=iter; i<solr; i++) {
        solp[i*solc+0] = iter;
        for(j=1;j<solc;j++) {
            solp[i*solc+j]=0.;
        }
    }
    gsl_multiroot_fsolver_free(s);
    OK
}

// working with the jacobian

typedef struct {int (*f)(int, double*, int, double *);
                int (*jf)(int, double*, int, int, double*);} Tfjf;

int f_aux(const gsl_vector*x, void *pars, gsl_vector*y) {
    Tfjf * fjf = ((Tfjf*) pars);
    double* p = (double*)calloc(x->size,sizeof(double));
    double* q = (double*)calloc(y->size,sizeof(double));
    int k;
    for(k=0;k<x->size;k++) {
        p[k] = gsl_vector_get(x,k);
    }
    (fjf->f)(x->size,p,y->size,q);
    for(k=0;k<y->size;k++) {
        gsl_vector_set(y,k,q[k]);
    }
    free(p);
    free(q);
    return 0;
}

int jf_aux(const gsl_vector * x, void * pars, gsl_matrix * jac) {
    Tfjf * fjf = ((Tfjf*) pars);
    double* p = (double*)calloc(x->size,sizeof(double));
    double* q = (double*)calloc((jac->size1)*(jac->size2),sizeof(double));
    int i,j,k;
    for(k=0;k<x->size;k++) {
        p[k] = gsl_vector_get(x,k);
    }

    (fjf->jf)(x->size,p,jac->size1,jac->size2,q);

    k=0;
    for(i=0;i<jac->size1;i++) {
        for(j=0;j<jac->size2;j++){
            gsl_matrix_set(jac,i,j,q[k++]);
        }
    }
    free(p);
    free(q);
    return 0;
}

int fjf_aux(const gsl_vector * x, void * pars, gsl_vector * f, gsl_matrix * g) {
    f_aux(x,pars,f);
    jf_aux(x,pars,g);
    return 0;
}

int multirootj(int method, int f(int, double*, int, double*),
                      int jac(int, double*, int, int, double*),
         double epsabs, int maxit,
         KRVEC(xi), RMAT(sol)) {
    REQUIRES(solr == maxit && solc == 1+2*xin,BAD_SIZE);
    DEBUGMSG("root_fjf");
    gsl_multiroot_function_fdf my_func;
    // extract function from pars
    my_func.f = f_aux;
    my_func.df = jf_aux;
    my_func.fdf = fjf_aux;
    my_func.n = xin;
    Tfjf stfjf;
    stfjf.f = f;
    stfjf.jf = jac;
    my_func.params = &stfjf;
    size_t iter = 0;
    int status;
    const gsl_multiroot_fdfsolver_type *T;
    gsl_multiroot_fdfsolver *s;
    // Starting point
    KDVVIEW(xi);
    switch(method) {
        case 0 : {T = gsl_multiroot_fdfsolver_hybridsj;; break; }
        case 1 : {T = gsl_multiroot_fdfsolver_hybridj; break; }
        case 2 : {T = gsl_multiroot_fdfsolver_newton; break; }
        case 3 : {T = gsl_multiroot_fdfsolver_gnewton; break; }
        default: ERROR(BAD_CODE);
    }
    s = gsl_multiroot_fdfsolver_alloc (T, my_func.n);

    gsl_multiroot_fdfsolver_set (s, &my_func, V(xi));

    do {
           status = gsl_multiroot_fdfsolver_iterate (s);

           solp[iter*solc+0] = iter+1;

           int k;
           for(k=0;k<xin;k++) {
               solp[iter*solc+k+1] = gsl_vector_get(s->x,k);
           }
           for(k=xin;k<2*xin;k++) {
               solp[iter*solc+k+1] = gsl_vector_get(s->f,k-xin);
           }

           iter++;
           if (status)   /* check if solver is stuck */
             break;

           status =
             gsl_multiroot_test_residual (s->f, epsabs);
        }
        while (status == GSL_CONTINUE && iter < maxit);

    int i,j;
    for (i=iter; i<solr; i++) {
        solp[i*solc+0] = iter;
        for(j=1;j<solc;j++) {
            solp[i*solc+j]=0.;
        }
    }
    gsl_multiroot_fdfsolver_free(s);
    OK
}

//-------------- non linear least squares fitting -------------------

int nlfit(int method, int f(int, double*, int, double*),
                      int jac(int, double*, int, int, double*),
         double epsabs, double epsrel, int maxit, int p,
         KRVEC(xi), RMAT(sol)) {
    REQUIRES(solr == maxit && solc == 2+xin,BAD_SIZE);
    DEBUGMSG("nlfit");
    const gsl_multifit_fdfsolver_type *T;
    gsl_multifit_fdfsolver *s;
    gsl_multifit_function_fdf my_f;
    // extract function from pars
    my_f.f = f_aux;
    my_f.df = jf_aux;
    my_f.fdf = fjf_aux;
    my_f.n = p;
    my_f.p = xin;  // !!!!
    Tfjf stfjf;
    stfjf.f = f;
    stfjf.jf = jac;
    my_f.params = &stfjf;
    size_t iter = 0;
    int status;

    KDVVIEW(xi);
    //DMVIEW(cov);

    switch(method) {
        case 0 : { T = gsl_multifit_fdfsolver_lmsder; break; }
        case 1 : { T = gsl_multifit_fdfsolver_lmder; break; }
        default: ERROR(BAD_CODE);
    }

    s = gsl_multifit_fdfsolver_alloc (T, my_f.n, my_f.p);
    gsl_multifit_fdfsolver_set (s, &my_f, V(xi));

    do {   status = gsl_multifit_fdfsolver_iterate (s);

           solp[iter*solc+0] = iter+1;
           solp[iter*solc+1] = gsl_blas_dnrm2 (s->f);

           int k;
           for(k=0;k<xin;k++) {
               solp[iter*solc+k+2] = gsl_vector_get(s->x,k);
           }

           iter++;
           if (status)   /* check if solver is stuck */
             break;

           status = gsl_multifit_test_delta (s->dx, s->x, epsabs, epsrel);
        }
        while (status == GSL_CONTINUE && iter < maxit);

    int i,j;
    for (i=iter; i<solr; i++) {
        solp[i*solc+0] = iter;
        for(j=1;j<solc;j++) {
            solp[i*solc+j]=0.;
        }
    }

    //gsl_multifit_covar (s->J, 0.0, M(cov));

    gsl_multifit_fdfsolver_free (s);
    OK
}


//////////////////////////////////////////////////////


#define RAN(C,F) case C: { for(k=0;k<rn;k++) { rp[k]= F(gen); }; OK }

int random_vector(int seed, int code, RVEC(r)) {
    DEBUGMSG("random_vector")
    static gsl_rng * gen = NULL;
    if (!gen) { gen = gsl_rng_alloc (gsl_rng_mt19937);}
    gsl_rng_set (gen, seed);
    int k;
    switch (code) {
        RAN(0,gsl_rng_uniform)
        RAN(1,gsl_ran_ugaussian)
        default: ERROR(BAD_CODE);
    }
}
#undef RAN

//////////////////////////////////////////////////////

#include "gsl-ode.c"

//////////////////////////////////////////////////////
