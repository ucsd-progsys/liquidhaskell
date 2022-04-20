#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include "lapack-aux.h"

#define MACRO(B) do {B} while (0)
#define ERROR(CODE) MACRO(return CODE;)
#define REQUIRES(COND, CODE) MACRO(if(!(COND)) {ERROR(CODE);})

#define MIN(A,B) ((A)<(B)?(A):(B))
#define MAX(A,B) ((A)>(B)?(A):(B))

// #define DBGL

#ifdef DBGL
#define DEBUGMSG(M) printf("\nLAPACK "M"\n");
#else
#define DEBUGMSG(M)
#endif

#define OK return 0;

// #ifdef DBGL
// #define DEBUGMSG(M) printf("LAPACK Wrapper "M"\n: "); size_t t0 = time(NULL);
// #define OK MACRO(printf("%ld s\n",time(0)-t0); return 0;);
// #else
// #define DEBUGMSG(M)
// #define OK return 0;
// #endif

#define TRACEMAT(M) {int q; printf(" %d x %d: ",M##r,M##c); \
                     for(q=0;q<M##r*M##c;q++) printf("%.1f ",M##p[q]); printf("\n");}

#define CHECK(RES,CODE) MACRO(if(RES) return CODE;)

#define BAD_SIZE 2000
#define BAD_CODE 2001
#define MEM      2002
#define BAD_FILE 2003
#define SINGULAR 2004
#define NOCONVER 2005
#define NODEFPOS 2006
#define NOSPRTD  2007

//---------------------------------------
void asm_finit() {
#ifdef i386

//  asm("finit");

    static unsigned char buf[108];
    asm("FSAVE %0":"=m" (buf));

    #if FPUDEBUG
    if(buf[8]!=255 || buf[9]!=255) {  // print warning in red
        printf("%c[;31mWarning: FPU TAG = %x %x\%c[0m\n",0x1B,buf[8],buf[9],0x1B);
    }
    #endif

    #if NANDEBUG
    asm("FRSTOR %0":"=m" (buf));
    #endif

#endif
}

//---------------------------------------

#if NANDEBUG

#define CHECKNANR(M,msg)                     \
{ int k;                                     \
for(k=0; k<(M##r * M##c); k++) {             \
    if(M##p[k] != M##p[k]) {                 \
        printf(msg);                         \
        TRACEMAT(M)                          \
        /*exit(1);*/                         \
    }                                        \
}                                            \
}

#define CHECKNANC(M,msg)                     \
{ int k;                                     \
for(k=0; k<(M##r * M##c); k++) {             \
    if(  M##p[k].r != M##p[k].r              \
      || M##p[k].i != M##p[k].i) {           \
        printf(msg);                         \
        /*exit(1);*/                         \
    }                                        \
}                                            \
}

#else
#define CHECKNANC(M,msg)
#define CHECKNANR(M,msg)
#endif

//---------------------------------------

//////////////////// real svd ////////////////////////////////////

/* Subroutine */ int dgesvd_(char *jobu, char *jobvt, integer *m, integer *n,
	doublereal *a, integer *lda, doublereal *s, doublereal *u, integer *
	ldu, doublereal *vt, integer *ldvt, doublereal *work, integer *lwork,
	integer *info);

int svd_l_R(KDMAT(a),DMAT(u), DVEC(s),DMAT(v)) {
    integer m = ar;
    integer n = ac;
    integer q = MIN(m,n);
    REQUIRES(sn==q,BAD_SIZE);
    REQUIRES(up==NULL || ur==m && (uc==m || uc==q),BAD_SIZE);
    char* jobu  = "A";
    if (up==NULL) {
        jobu = "N";
    } else {
        if (uc==q) {
            jobu = "S";
        }
    }
    REQUIRES(vp==NULL || vc==n && (vr==n || vr==q),BAD_SIZE);
    char* jobvt  = "A";
    integer ldvt = n;
    if (vp==NULL) {
        jobvt = "N";
    } else {
        if (vr==q) {
            jobvt = "S";
            ldvt = q;
        }
    }
    DEBUGMSG("svd_l_R");
    double *B = (double*)malloc(m*n*sizeof(double));
    CHECK(!B,MEM);
    memcpy(B,ap,m*n*sizeof(double));
    integer lwork = -1;
    integer res;
    // ask for optimal lwork
    double ans;
    dgesvd_ (jobu,jobvt,
             &m,&n,B,&m,
             sp,
             up,&m,
             vp,&ldvt,
             &ans, &lwork,
             &res);
    lwork = ceil(ans);
    double * work = (double*)malloc(lwork*sizeof(double));
    CHECK(!work,MEM);
    dgesvd_ (jobu,jobvt,
             &m,&n,B,&m,
             sp,
             up,&m,
             vp,&ldvt,
             work, &lwork,
             &res);
    CHECK(res,res);
    free(work);
    free(B);
    OK
}

// (alternative version)

/* Subroutine */ int dgesdd_(char *jobz, integer *m, integer *n, doublereal *
	a, integer *lda, doublereal *s, doublereal *u, integer *ldu,
	doublereal *vt, integer *ldvt, doublereal *work, integer *lwork,
	integer *iwork, integer *info);

int svd_l_Rdd(KDMAT(a),DMAT(u), DVEC(s),DMAT(v)) {
    integer m = ar;
    integer n = ac;
    integer q = MIN(m,n);
    REQUIRES(sn==q,BAD_SIZE);
    REQUIRES(up == NULL && vp == NULL
             || ur==m && vc==n
                &&   (uc == q && vr == q
                   || uc == m && vc==n),BAD_SIZE);
    char* jobz  = "A";
    integer ldvt = n;
    if (up==NULL) {
        jobz = "N";
    } else {
        if (uc==q && vr == q) {
            jobz = "S";
            ldvt = q;
        }
    }
    DEBUGMSG("svd_l_Rdd");
    double *B = (double*)malloc(m*n*sizeof(double));
    CHECK(!B,MEM);
    memcpy(B,ap,m*n*sizeof(double));
    integer* iwk = (integer*) malloc(8*q*sizeof(integer));
    CHECK(!iwk,MEM);
    integer lwk = -1;
    integer res;
    // ask for optimal lwk
    double ans;
    dgesdd_ (jobz,&m,&n,B,&m,sp,up,&m,vp,&ldvt,&ans,&lwk,iwk,&res);
    lwk = ans;
    double * workv = (double*)malloc(lwk*sizeof(double));
    CHECK(!workv,MEM);
    dgesdd_ (jobz,&m,&n,B,&m,sp,up,&m,vp,&ldvt,workv,&lwk,iwk,&res);
    CHECK(res,res);
    free(iwk);
    free(workv);
    free(B);
    OK
}

//////////////////// complex svd ////////////////////////////////////

// not in clapack.h

int zgesvd_(char *jobu, char *jobvt, integer *m, integer *n,
    doublecomplex *a, integer *lda, doublereal *s, doublecomplex *u,
    integer *ldu, doublecomplex *vt, integer *ldvt, doublecomplex *work,
    integer *lwork, doublereal *rwork, integer *info);

int svd_l_C(KCMAT(a),CMAT(u), DVEC(s),CMAT(v)) {
    integer m = ar;
    integer n = ac;
    integer q = MIN(m,n);
    REQUIRES(sn==q,BAD_SIZE);
    REQUIRES(up==NULL || ur==m && (uc==m || uc==q),BAD_SIZE);
    char* jobu  = "A";
    if (up==NULL) {
        jobu = "N";
    } else {
        if (uc==q) {
            jobu = "S";
        }
    }
    REQUIRES(vp==NULL || vc==n && (vr==n || vr==q),BAD_SIZE);
    char* jobvt  = "A";
    integer ldvt = n;
    if (vp==NULL) {
        jobvt = "N";
    } else {
        if (vr==q) {
            jobvt = "S";
            ldvt = q;
        }
    }DEBUGMSG("svd_l_C");
    doublecomplex *B = (doublecomplex*)malloc(m*n*sizeof(doublecomplex));
    CHECK(!B,MEM);
    memcpy(B,ap,m*n*sizeof(doublecomplex));

    double *rwork = (double*) malloc(5*q*sizeof(double));
    CHECK(!rwork,MEM);
    integer lwork = -1;
    integer res;
    // ask for optimal lwork
    doublecomplex ans;
    zgesvd_ (jobu,jobvt,
             &m,&n,B,&m,
             sp,
             up,&m,
             vp,&ldvt,
             &ans, &lwork,
             rwork,
             &res);
    lwork = ceil(ans.r);
    doublecomplex * work = (doublecomplex*)malloc(lwork*sizeof(doublecomplex));
    CHECK(!work,MEM);
    zgesvd_ (jobu,jobvt,
             &m,&n,B,&m,
             sp,
             up,&m,
             vp,&ldvt,
             work, &lwork,
             rwork,
             &res);
    CHECK(res,res);
    free(work);
    free(rwork);
    free(B);
    OK
}

int zgesdd_ (char *jobz, integer *m, integer *n,
    doublecomplex *a, integer *lda, doublereal *s, doublecomplex *u,
    integer *ldu, doublecomplex *vt, integer *ldvt, doublecomplex *work,
    integer *lwork, doublereal *rwork, integer* iwork, integer *info);

int svd_l_Cdd(KCMAT(a),CMAT(u), DVEC(s),CMAT(v)) {
    //printf("entro\n");
    integer m = ar;
    integer n = ac;
    integer q = MIN(m,n);
    REQUIRES(sn==q,BAD_SIZE);
    REQUIRES(up == NULL && vp == NULL
             || ur==m && vc==n
                &&   (uc == q && vr == q
                   || uc == m && vc==n),BAD_SIZE);
    char* jobz  = "A";
    integer ldvt = n;
    if (up==NULL) {
        jobz = "N";
    } else {
        if (uc==q && vr == q) {
            jobz = "S";
            ldvt = q;
        }
    }
    DEBUGMSG("svd_l_Cdd");
    doublecomplex *B = (doublecomplex*)malloc(m*n*sizeof(doublecomplex));
    CHECK(!B,MEM);
    memcpy(B,ap,m*n*sizeof(doublecomplex));
    integer* iwk = (integer*) malloc(8*q*sizeof(integer));
    CHECK(!iwk,MEM);
    int lrwk;
    if (0 && *jobz == 'N') {
        lrwk = 5*q; // does not work, crash at free below
    } else {
        lrwk = 5*q*q + 7*q;
    }
    double *rwk = (double*)malloc(lrwk*sizeof(double));;
    CHECK(!rwk,MEM);
    //printf("%s %ld %d\n",jobz,q,lrwk);
    integer lwk = -1;
    integer res;
    // ask for optimal lwk
    doublecomplex ans;
    zgesdd_ (jobz,&m,&n,B,&m,sp,up,&m,vp,&ldvt,&ans,&lwk,rwk,iwk,&res);
    lwk = ans.r;
    //printf("lwk = %ld\n",lwk);
    doublecomplex * workv = (doublecomplex*)malloc(lwk*sizeof(doublecomplex));
    CHECK(!workv,MEM);
    zgesdd_ (jobz,&m,&n,B,&m,sp,up,&m,vp,&ldvt,workv,&lwk,rwk,iwk,&res);
    //printf("res = %ld\n",res);
    CHECK(res,res);
    free(workv); // printf("freed workv\n");
    free(rwk);   // printf("freed rwk\n");
    free(iwk);   // printf("freed iwk\n");
    free(B);     // printf("freed B, salgo\n");
    OK
}

//////////////////// general complex eigensystem ////////////

/* Subroutine */ int zgeev_(char *jobvl, char *jobvr, integer *n,
	doublecomplex *a, integer *lda, doublecomplex *w, doublecomplex *vl,
	integer *ldvl, doublecomplex *vr, integer *ldvr, doublecomplex *work,
	integer *lwork, doublereal *rwork, integer *info);

int eig_l_C(KCMAT(a), CMAT(u), CVEC(s),CMAT(v)) {
    integer n = ar;
    REQUIRES(ac==n && sn==n, BAD_SIZE);
    REQUIRES(up==NULL || ur==n && uc==n, BAD_SIZE);
    char jobvl = up==NULL?'N':'V';
    REQUIRES(vp==NULL || vr==n && vc==n, BAD_SIZE);
    char jobvr = vp==NULL?'N':'V';
    DEBUGMSG("eig_l_C");
    doublecomplex *B = (doublecomplex*)malloc(n*n*sizeof(doublecomplex));
    CHECK(!B,MEM);
    memcpy(B,ap,n*n*sizeof(doublecomplex));
    double *rwork = (double*) malloc(2*n*sizeof(double));
    CHECK(!rwork,MEM);
    integer lwork = -1;
    integer res;
    // ask for optimal lwork
    doublecomplex ans;
    //printf("ask zgeev\n");
    zgeev_  (&jobvl,&jobvr,
             &n,B,&n,
             sp,
             up,&n,
             vp,&n,
             &ans, &lwork,
             rwork,
             &res);
    lwork = ceil(ans.r);
    //printf("ans = %d\n",lwork);
    doublecomplex * work = (doublecomplex*)malloc(lwork*sizeof(doublecomplex));
    CHECK(!work,MEM);
    //printf("zgeev\n");
    zgeev_  (&jobvl,&jobvr,
             &n,B,&n,
             sp,
             up,&n,
             vp,&n,
             work, &lwork,
             rwork,
             &res);
    CHECK(res,res);
    free(work);
    free(rwork);
    free(B);
    OK
}



//////////////////// general real eigensystem ////////////

/* Subroutine */ int dgeev_(char *jobvl, char *jobvr, integer *n, doublereal *
	a, integer *lda, doublereal *wr, doublereal *wi, doublereal *vl,
	integer *ldvl, doublereal *vr, integer *ldvr, doublereal *work,
	integer *lwork, integer *info);

int eig_l_R(KDMAT(a),DMAT(u), CVEC(s),DMAT(v)) {
    integer n = ar;
    REQUIRES(ac==n && sn==n, BAD_SIZE);
    REQUIRES(up==NULL || ur==n && uc==n, BAD_SIZE);
    char jobvl = up==NULL?'N':'V';
    REQUIRES(vp==NULL || vr==n && vc==n, BAD_SIZE);
    char jobvr = vp==NULL?'N':'V';
    DEBUGMSG("eig_l_R");
    double *B = (double*)malloc(n*n*sizeof(double));
    CHECK(!B,MEM);
    memcpy(B,ap,n*n*sizeof(double));
    integer lwork = -1;
    integer res;
    // ask for optimal lwork
    double ans;
    //printf("ask dgeev\n");
    dgeev_  (&jobvl,&jobvr,
             &n,B,&n,
             (double*)sp, (double*)sp+n,
             up,&n,
             vp,&n,
             &ans, &lwork,
             &res);
    lwork = ceil(ans);
    //printf("ans = %d\n",lwork);
    double * work = (double*)malloc(lwork*sizeof(double));
    CHECK(!work,MEM);
    //printf("dgeev\n");
    dgeev_  (&jobvl,&jobvr,
             &n,B,&n,
             (double*)sp, (double*)sp+n,
             up,&n,
             vp,&n,
             work, &lwork,
             &res);
    CHECK(res,res);
    free(work);
    free(B);
    OK
}


//////////////////// symmetric real eigensystem ////////////

/* Subroutine */ int dsyev_(char *jobz, char *uplo, integer *n, doublereal *a,
	 integer *lda, doublereal *w, doublereal *work, integer *lwork,
	integer *info);

int eig_l_S(int wantV,KDMAT(a),DVEC(s),DMAT(v)) {
    integer n = ar;
    REQUIRES(ac==n && sn==n, BAD_SIZE);
    REQUIRES(vr==n && vc==n, BAD_SIZE);
    char jobz = wantV?'V':'N';
    DEBUGMSG("eig_l_S");
    memcpy(vp,ap,n*n*sizeof(double));
    integer lwork = -1;
    char uplo = 'U';
    integer res;
    // ask for optimal lwork
    double ans;
    //printf("ask dsyev\n");
    dsyev_  (&jobz,&uplo,
             &n,vp,&n,
             sp,
             &ans, &lwork,
             &res);
    lwork = ceil(ans);
    //printf("ans = %d\n",lwork);
    double * work = (double*)malloc(lwork*sizeof(double));
    CHECK(!work,MEM);
    dsyev_  (&jobz,&uplo,
             &n,vp,&n,
             sp,
             work, &lwork,
             &res);
    CHECK(res,res);
    free(work);
    OK
}

//////////////////// hermitian complex eigensystem ////////////

/* Subroutine */ int zheev_(char *jobz, char *uplo, integer *n, doublecomplex
	*a, integer *lda, doublereal *w, doublecomplex *work, integer *lwork,
	doublereal *rwork, integer *info);

int eig_l_H(int wantV,KCMAT(a),DVEC(s),CMAT(v)) {
    integer n = ar;
    REQUIRES(ac==n && sn==n, BAD_SIZE);
    REQUIRES(vr==n && vc==n, BAD_SIZE);
    char jobz = wantV?'V':'N';
    DEBUGMSG("eig_l_H");
    memcpy(vp,ap,2*n*n*sizeof(double));
    double *rwork = (double*) malloc((3*n-2)*sizeof(double));
    CHECK(!rwork,MEM);
    integer lwork = -1;
    char uplo = 'U';
    integer res;
    // ask for optimal lwork
    doublecomplex ans;
    //printf("ask zheev\n");
    zheev_  (&jobz,&uplo,
             &n,vp,&n,
             sp,
             &ans, &lwork,
             rwork,
             &res);
    lwork = ceil(ans.r);
    //printf("ans = %d\n",lwork);
    doublecomplex * work = (doublecomplex*)malloc(lwork*sizeof(doublecomplex));
    CHECK(!work,MEM);
    zheev_  (&jobz,&uplo,
             &n,vp,&n,
             sp,
             work, &lwork,
             rwork,
             &res);
    CHECK(res,res);
    free(work);
    free(rwork);
    OK
}

//////////////////// general real linear system ////////////

/* Subroutine */ int dgesv_(integer *n, integer *nrhs, doublereal *a, integer
	*lda, integer *ipiv, doublereal *b, integer *ldb, integer *info);

int linearSolveR_l(KDMAT(a),KDMAT(b),DMAT(x)) {
    integer n = ar;
    integer nhrs = bc;
    REQUIRES(n>=1 && ar==ac && ar==br,BAD_SIZE);
    DEBUGMSG("linearSolveR_l");
    double*AC = (double*)malloc(n*n*sizeof(double));
    memcpy(AC,ap,n*n*sizeof(double));
    memcpy(xp,bp,n*nhrs*sizeof(double));
    integer * ipiv = (integer*)malloc(n*sizeof(integer));
    integer res;
    dgesv_  (&n,&nhrs,
             AC, &n,
             ipiv,
             xp, &n,
             &res);
    if(res>0) {
        return SINGULAR;
    }
    CHECK(res,res);
    free(ipiv);
    free(AC);
    OK
}

//////////////////// general complex linear system ////////////

/* Subroutine */ int zgesv_(integer *n, integer *nrhs, doublecomplex *a,
	integer *lda, integer *ipiv, doublecomplex *b, integer *ldb, integer *
	info);

int linearSolveC_l(KCMAT(a),KCMAT(b),CMAT(x)) {
    integer n = ar;
    integer nhrs = bc;
    REQUIRES(n>=1 && ar==ac && ar==br,BAD_SIZE);
    DEBUGMSG("linearSolveC_l");
    doublecomplex*AC = (doublecomplex*)malloc(n*n*sizeof(doublecomplex));
    memcpy(AC,ap,n*n*sizeof(doublecomplex));
    memcpy(xp,bp,n*nhrs*sizeof(doublecomplex));
    integer * ipiv = (integer*)malloc(n*sizeof(integer));
    integer res;
    zgesv_  (&n,&nhrs,
             AC, &n,
             ipiv,
             xp, &n,
             &res);
    if(res>0) {
        return SINGULAR;
    }
    CHECK(res,res);
    free(ipiv);
    free(AC);
    OK
}

//////// symmetric positive definite real linear system using Cholesky ////////////

/* Subroutine */ int dpotrs_(char *uplo, integer *n, integer *nrhs,
	doublereal *a, integer *lda, doublereal *b, integer *ldb, integer *
	info);

int cholSolveR_l(KDMAT(a),KDMAT(b),DMAT(x)) {
    integer n = ar;
    integer nhrs = bc;
    REQUIRES(n>=1 && ar==ac && ar==br,BAD_SIZE);
    DEBUGMSG("cholSolveR_l");
    memcpy(xp,bp,n*nhrs*sizeof(double));
    integer res;
    dpotrs_ ("U",
             &n,&nhrs,
             (double*)ap, &n,
             xp, &n,
             &res);
    CHECK(res,res);
    OK
}

//////// Hermitian positive definite real linear system using Cholesky ////////////

/* Subroutine */ int zpotrs_(char *uplo, integer *n, integer *nrhs,
	doublecomplex *a, integer *lda, doublecomplex *b, integer *ldb,
	integer *info);

int cholSolveC_l(KCMAT(a),KCMAT(b),CMAT(x)) {
    integer n = ar;
    integer nhrs = bc;
    REQUIRES(n>=1 && ar==ac && ar==br,BAD_SIZE);
    DEBUGMSG("cholSolveC_l");
    memcpy(xp,bp,n*nhrs*sizeof(doublecomplex));
    integer res;
    zpotrs_  ("U",
             &n,&nhrs,
             (doublecomplex*)ap, &n,
             xp, &n,
             &res);
    CHECK(res,res);
    OK
}

//////////////////// least squares real linear system ////////////

/* Subroutine */ int dgels_(char *trans, integer *m, integer *n, integer *
	nrhs, doublereal *a, integer *lda, doublereal *b, integer *ldb,
	doublereal *work, integer *lwork, integer *info);

int linearSolveLSR_l(KDMAT(a),KDMAT(b),DMAT(x)) {
    integer m = ar;
    integer n = ac;
    integer nrhs = bc;
    integer ldb = xr;
    REQUIRES(m>=1 && n>=1 && ar==br && xr==MAX(m,n) && xc == bc, BAD_SIZE);
    DEBUGMSG("linearSolveLSR_l");
    double*AC = (double*)malloc(m*n*sizeof(double));
    memcpy(AC,ap,m*n*sizeof(double));
    if (m>=n) {
        memcpy(xp,bp,m*nrhs*sizeof(double));
    } else {
        int k;
        for(k = 0; k<nrhs; k++) {
            memcpy(xp+ldb*k,bp+m*k,m*sizeof(double));
        }
    }
    integer res;
    integer lwork = -1;
    double ans;
    dgels_  ("N",&m,&n,&nrhs,
             AC,&m,
             xp,&ldb,
             &ans,&lwork,
             &res);
    lwork = ceil(ans);
    //printf("ans = %d\n",lwork);
    double * work = (double*)malloc(lwork*sizeof(double));
    dgels_  ("N",&m,&n,&nrhs,
             AC,&m,
             xp,&ldb,
             work,&lwork,
             &res);
    if(res>0) {
        return SINGULAR;
    }
    CHECK(res,res);
    free(work);
    free(AC);
    OK
}

//////////////////// least squares complex linear system ////////////

/* Subroutine */ int zgels_(char *trans, integer *m, integer *n, integer *
	nrhs, doublecomplex *a, integer *lda, doublecomplex *b, integer *ldb,
	doublecomplex *work, integer *lwork, integer *info);

int linearSolveLSC_l(KCMAT(a),KCMAT(b),CMAT(x)) {
    integer m = ar;
    integer n = ac;
    integer nrhs = bc;
    integer ldb = xr;
    REQUIRES(m>=1 && n>=1 && ar==br && xr==MAX(m,n) && xc == bc, BAD_SIZE);
    DEBUGMSG("linearSolveLSC_l");
    doublecomplex*AC = (doublecomplex*)malloc(m*n*sizeof(doublecomplex));
    memcpy(AC,ap,m*n*sizeof(doublecomplex));
    if (m>=n) {
        memcpy(xp,bp,m*nrhs*sizeof(doublecomplex));
    } else {
        int k;
        for(k = 0; k<nrhs; k++) {
            memcpy(xp+ldb*k,bp+m*k,m*sizeof(doublecomplex));
        }
    }
    integer res;
    integer lwork = -1;
    doublecomplex ans;
    zgels_  ("N",&m,&n,&nrhs,
             AC,&m,
             xp,&ldb,
             &ans,&lwork,
             &res);
    lwork = ceil(ans.r);
    //printf("ans = %d\n",lwork);
    doublecomplex * work = (doublecomplex*)malloc(lwork*sizeof(doublecomplex));
    zgels_  ("N",&m,&n,&nrhs,
             AC,&m,
             xp,&ldb,
             work,&lwork,
             &res);
    if(res>0) {
        return SINGULAR;
    }
    CHECK(res,res);
    free(work);
    free(AC);
    OK
}

//////////////////// least squares real linear system using SVD ////////////

/* Subroutine */ int dgelss_(integer *m, integer *n, integer *nrhs,
	doublereal *a, integer *lda, doublereal *b, integer *ldb, doublereal *
	s, doublereal *rcond, integer *rank, doublereal *work, integer *lwork,
	 integer *info);

int linearSolveSVDR_l(double rcond,KDMAT(a),KDMAT(b),DMAT(x)) {
    integer m = ar;
    integer n = ac;
    integer nrhs = bc;
    integer ldb = xr;
    REQUIRES(m>=1 && n>=1 && ar==br && xr==MAX(m,n) && xc == bc, BAD_SIZE);
    DEBUGMSG("linearSolveSVDR_l");
    double*AC = (double*)malloc(m*n*sizeof(double));
    double*S = (double*)malloc(MIN(m,n)*sizeof(double));
    memcpy(AC,ap,m*n*sizeof(double));
    if (m>=n) {
        memcpy(xp,bp,m*nrhs*sizeof(double));
    } else {
        int k;
        for(k = 0; k<nrhs; k++) {
            memcpy(xp+ldb*k,bp+m*k,m*sizeof(double));
        }
    }
    integer res;
    integer lwork = -1;
    integer rank;
    double ans;
    dgelss_  (&m,&n,&nrhs,
             AC,&m,
             xp,&ldb,
             S,
             &rcond,&rank,
             &ans,&lwork,
             &res);
    lwork = ceil(ans);
    //printf("ans = %d\n",lwork);
    double * work = (double*)malloc(lwork*sizeof(double));
    dgelss_  (&m,&n,&nrhs,
             AC,&m,
             xp,&ldb,
             S,
             &rcond,&rank,
             work,&lwork,
             &res);
    if(res>0) {
        return NOCONVER;
    }
    CHECK(res,res);
    free(work);
    free(S);
    free(AC);
    OK
}

//////////////////// least squares complex linear system using SVD ////////////

// not in clapack.h

int zgelss_(integer *m, integer *n, integer *nhrs,
    doublecomplex *a, integer *lda, doublecomplex *b, integer *ldb, doublereal *s,
    doublereal *rcond, integer* rank,
    doublecomplex *work, integer* lwork, doublereal* rwork,
    integer *info);

int linearSolveSVDC_l(double rcond, KCMAT(a),KCMAT(b),CMAT(x)) {
    integer m = ar;
    integer n = ac;
    integer nrhs = bc;
    integer ldb = xr;
    REQUIRES(m>=1 && n>=1 && ar==br && xr==MAX(m,n) && xc == bc, BAD_SIZE);
    DEBUGMSG("linearSolveSVDC_l");
    doublecomplex*AC = (doublecomplex*)malloc(m*n*sizeof(doublecomplex));
    double*S = (double*)malloc(MIN(m,n)*sizeof(double));
    double*RWORK = (double*)malloc(5*MIN(m,n)*sizeof(double));
    memcpy(AC,ap,m*n*sizeof(doublecomplex));
    if (m>=n) {
        memcpy(xp,bp,m*nrhs*sizeof(doublecomplex));
    } else {
        int k;
        for(k = 0; k<nrhs; k++) {
            memcpy(xp+ldb*k,bp+m*k,m*sizeof(doublecomplex));
        }
    }
    integer res;
    integer lwork = -1;
    integer rank;
    doublecomplex ans;
    zgelss_  (&m,&n,&nrhs,
             AC,&m,
             xp,&ldb,
             S,
             &rcond,&rank,
             &ans,&lwork,
             RWORK,
             &res);
    lwork = ceil(ans.r);
    //printf("ans = %d\n",lwork);
    doublecomplex * work = (doublecomplex*)malloc(lwork*sizeof(doublecomplex));
    zgelss_  (&m,&n,&nrhs,
             AC,&m,
             xp,&ldb,
             S,
             &rcond,&rank,
             work,&lwork,
             RWORK,
             &res);
    if(res>0) {
        return NOCONVER;
    }
    CHECK(res,res);
    free(work);
    free(RWORK);
    free(S);
    free(AC);
    OK
}

//////////////////// Cholesky factorization /////////////////////////

/* Subroutine */ int zpotrf_(char *uplo, integer *n, doublecomplex *a,
	integer *lda, integer *info);

int chol_l_H(KCMAT(a),CMAT(l)) {
    integer n = ar;
    REQUIRES(n>=1 && ac == n && lr==n && lc==n,BAD_SIZE);
    DEBUGMSG("chol_l_H");
    memcpy(lp,ap,n*n*sizeof(doublecomplex));
    char uplo = 'U';
    integer res;
    zpotrf_ (&uplo,&n,lp,&n,&res);
    CHECK(res>0,NODEFPOS);
    CHECK(res,res);
    doublecomplex zero = {0.,0.};
    int r,c;
    for (r=0; r<lr-1; r++) {
        for(c=r+1; c<lc; c++) {
            lp[r*lc+c] = zero;
        }
    }
    OK
}


/* Subroutine */ int dpotrf_(char *uplo, integer *n, doublereal *a, integer *
	lda, integer *info);

int chol_l_S(KDMAT(a),DMAT(l)) {
    integer n = ar;
    REQUIRES(n>=1 && ac == n && lr==n && lc==n,BAD_SIZE);
    DEBUGMSG("chol_l_S");
    memcpy(lp,ap,n*n*sizeof(double));
    char uplo = 'U';
    integer res;
    dpotrf_ (&uplo,&n,lp,&n,&res);
    CHECK(res>0,NODEFPOS);
    CHECK(res,res);
    int r,c;
    for (r=0; r<lr-1; r++) {
        for(c=r+1; c<lc; c++) {
            lp[r*lc+c] = 0.;
        }
    }
    OK
}

//////////////////// QR factorization /////////////////////////

/* Subroutine */ int dgeqr2_(integer *m, integer *n, doublereal *a, integer *
	lda, doublereal *tau, doublereal *work, integer *info);

int qr_l_R(KDMAT(a), DVEC(tau), DMAT(r)) {
    integer m = ar;
    integer n = ac;
    integer mn = MIN(m,n);
    REQUIRES(m>=1 && n >=1 && rr== m && rc == n && taun == mn, BAD_SIZE);
    DEBUGMSG("qr_l_R");
    double *WORK = (double*)malloc(n*sizeof(double));
    CHECK(!WORK,MEM);
    memcpy(rp,ap,m*n*sizeof(double));
    integer res;
    dgeqr2_ (&m,&n,rp,&m,taup,WORK,&res);
    CHECK(res,res);
    free(WORK);
    OK
}

/* Subroutine */ int zgeqr2_(integer *m, integer *n, doublecomplex *a,
	integer *lda, doublecomplex *tau, doublecomplex *work, integer *info);

int qr_l_C(KCMAT(a), CVEC(tau), CMAT(r)) {
    integer m = ar;
    integer n = ac;
    integer mn = MIN(m,n);
    REQUIRES(m>=1 && n >=1 && rr== m && rc == n && taun == mn, BAD_SIZE);
    DEBUGMSG("qr_l_C");
    doublecomplex *WORK = (doublecomplex*)malloc(n*sizeof(doublecomplex));
    CHECK(!WORK,MEM);
    memcpy(rp,ap,m*n*sizeof(doublecomplex));
    integer res;
    zgeqr2_ (&m,&n,rp,&m,taup,WORK,&res);
    CHECK(res,res);
    free(WORK);
    OK
}

//////////////////// Hessenberg factorization /////////////////////////

/* Subroutine */ int dgehrd_(integer *n, integer *ilo, integer *ihi,
	doublereal *a, integer *lda, doublereal *tau, doublereal *work,
	integer *lwork, integer *info);

int hess_l_R(KDMAT(a), DVEC(tau), DMAT(r)) {
    integer m = ar;
    integer n = ac;
    integer mn = MIN(m,n);
    REQUIRES(m>=1 && n == m && rr== m && rc == n && taun == mn-1, BAD_SIZE);
    DEBUGMSG("hess_l_R");
    integer lwork = 5*n; // fixme
    double *WORK = (double*)malloc(lwork*sizeof(double));
    CHECK(!WORK,MEM);
    memcpy(rp,ap,m*n*sizeof(double));
    integer res;
    integer one = 1;
    dgehrd_ (&n,&one,&n,rp,&n,taup,WORK,&lwork,&res);
    CHECK(res,res);
    free(WORK);
    OK
}


/* Subroutine */ int zgehrd_(integer *n, integer *ilo, integer *ihi,
	doublecomplex *a, integer *lda, doublecomplex *tau, doublecomplex *
	work, integer *lwork, integer *info);

int hess_l_C(KCMAT(a), CVEC(tau), CMAT(r)) {
    integer m = ar;
    integer n = ac;
    integer mn = MIN(m,n);
    REQUIRES(m>=1 && n == m && rr== m && rc == n && taun == mn-1, BAD_SIZE);
    DEBUGMSG("hess_l_C");
    integer lwork = 5*n; // fixme
    doublecomplex *WORK = (doublecomplex*)malloc(lwork*sizeof(doublecomplex));
    CHECK(!WORK,MEM);
    memcpy(rp,ap,m*n*sizeof(doublecomplex));
    integer res;
    integer one = 1;
    zgehrd_ (&n,&one,&n,rp,&n,taup,WORK,&lwork,&res);
    CHECK(res,res);
    free(WORK);
    OK
}

//////////////////// Schur factorization /////////////////////////

/* Subroutine */ int dgees_(char *jobvs, char *sort, L_fp select, integer *n,
	doublereal *a, integer *lda, integer *sdim, doublereal *wr,
	doublereal *wi, doublereal *vs, integer *ldvs, doublereal *work,
	integer *lwork, logical *bwork, integer *info);

int schur_l_R(KDMAT(a), DMAT(u), DMAT(s)) {
    integer m = ar;
    integer n = ac;
    REQUIRES(m>=1 && n==m && ur==n && uc==n && sr==n && sc==n, BAD_SIZE);
    DEBUGMSG("schur_l_R");
    int k;
    //printf("---------------------------\n");
    //printf("%p: ",ap); for(k=0;k<n*n;k++) printf("%f ",ap[k]); printf("\n");
    //printf("%p: ",up); for(k=0;k<n*n;k++) printf("%f ",up[k]); printf("\n");
    //printf("%p: ",sp); for(k=0;k<n*n;k++) printf("%f ",sp[k]); printf("\n");
    memcpy(sp,ap,n*n*sizeof(double));
    integer lwork = 6*n; // fixme
    double *WORK = (double*)malloc(lwork*sizeof(double));
    double *WR = (double*)malloc(n*sizeof(double));
    double *WI = (double*)malloc(n*sizeof(double));
    // WR and WI not really required in this call
    logical *BWORK = (logical*)malloc(n*sizeof(logical));
    integer res;
    integer sdim;
    dgees_ ("V","N",NULL,&n,sp,&n,&sdim,WR,WI,up,&n,WORK,&lwork,BWORK,&res);
    //printf("%p: ",ap); for(k=0;k<n*n;k++) printf("%f ",ap[k]); printf("\n");
    //printf("%p: ",up); for(k=0;k<n*n;k++) printf("%f ",up[k]); printf("\n");
    //printf("%p: ",sp); for(k=0;k<n*n;k++) printf("%f ",sp[k]); printf("\n");
    if(res>0) {
        return NOCONVER;
    }
    CHECK(res,res);
    free(WR);
    free(WI);
    free(BWORK);
    free(WORK);
    OK
}


/* Subroutine */ int zgees_(char *jobvs, char *sort, L_fp select, integer *n,
	doublecomplex *a, integer *lda, integer *sdim, doublecomplex *w,
	doublecomplex *vs, integer *ldvs, doublecomplex *work, integer *lwork,
	 doublereal *rwork, logical *bwork, integer *info);

int schur_l_C(KCMAT(a), CMAT(u), CMAT(s)) {
    integer m = ar;
    integer n = ac;
    REQUIRES(m>=1 && n==m && ur==n && uc==n && sr==n && sc==n, BAD_SIZE);
    DEBUGMSG("schur_l_C");
    memcpy(sp,ap,n*n*sizeof(doublecomplex));
    integer lwork = 6*n; // fixme
    doublecomplex *WORK = (doublecomplex*)malloc(lwork*sizeof(doublecomplex));
    doublecomplex *W = (doublecomplex*)malloc(n*sizeof(doublecomplex));
    // W not really required in this call
    logical *BWORK = (logical*)malloc(n*sizeof(logical));
    double *RWORK = (double*)malloc(n*sizeof(double));
    integer res;
    integer sdim;
    zgees_ ("V","N",NULL,&n,sp,&n,&sdim,W,
                            up,&n,
                            WORK,&lwork,RWORK,BWORK,&res);
    if(res>0) {
        return NOCONVER;
    }
    CHECK(res,res);
    free(W);
    free(BWORK);
    free(WORK);
    OK
}

//////////////////// LU factorization /////////////////////////

/* Subroutine */ int dgetrf_(integer *m, integer *n, doublereal *a, integer *
	lda, integer *ipiv, integer *info);

int lu_l_R(KDMAT(a), DVEC(ipiv), DMAT(r)) {
    integer m = ar;
    integer n = ac;
    integer mn = MIN(m,n);
    REQUIRES(m>=1 && n >=1 && ipivn == mn, BAD_SIZE);
    DEBUGMSG("lu_l_R");
    integer* auxipiv = (integer*)malloc(mn*sizeof(integer));
    memcpy(rp,ap,m*n*sizeof(double));
    integer res;
    dgetrf_ (&m,&n,rp,&m,auxipiv,&res);
    if(res>0) {
        res = 0; // fixme
    }
    CHECK(res,res);
    int k;
    for (k=0; k<mn; k++) {
        ipivp[k] = auxipiv[k];
    }
    free(auxipiv);
    OK
}


/* Subroutine */ int zgetrf_(integer *m, integer *n, doublecomplex *a,
	integer *lda, integer *ipiv, integer *info);

int lu_l_C(KCMAT(a), DVEC(ipiv), CMAT(r)) {
    integer m = ar;
    integer n = ac;
    integer mn = MIN(m,n);
    REQUIRES(m>=1 && n >=1 && ipivn == mn, BAD_SIZE);
    DEBUGMSG("lu_l_C");
    integer* auxipiv = (integer*)malloc(mn*sizeof(integer));
    memcpy(rp,ap,m*n*sizeof(doublecomplex));
    integer res;
    zgetrf_ (&m,&n,rp,&m,auxipiv,&res);
    if(res>0) {
        res = 0; // fixme
    }
    CHECK(res,res);
    int k;
    for (k=0; k<mn; k++) {
        ipivp[k] = auxipiv[k];
    }
    free(auxipiv);
    OK
}


//////////////////// LU substitution /////////////////////////

/* Subroutine */ int dgetrs_(char *trans, integer *n, integer *nrhs,
	doublereal *a, integer *lda, integer *ipiv, doublereal *b, integer *
	ldb, integer *info);

int luS_l_R(KDMAT(a), KDVEC(ipiv), KDMAT(b), DMAT(x)) {
  integer m = ar;
  integer n = ac;
  integer mrhs = br;
  integer nrhs = bc;

  REQUIRES(m==n && m==mrhs && m==ipivn,BAD_SIZE);
  integer* auxipiv = (integer*)malloc(n*sizeof(integer));
  int k;
  for (k=0; k<n; k++) {
    auxipiv[k] = (integer)ipivp[k];
  }
  integer res;
  memcpy(xp,bp,mrhs*nrhs*sizeof(double));
  dgetrs_ ("N",&n,&nrhs,(/*no const (!?)*/ double*)ap,&m,auxipiv,xp,&mrhs,&res);
  CHECK(res,res);
  free(auxipiv);
  OK
}


/* Subroutine */ int zgetrs_(char *trans, integer *n, integer *nrhs,
	doublecomplex *a, integer *lda, integer *ipiv, doublecomplex *b,
	integer *ldb, integer *info);

int luS_l_C(KCMAT(a), KDVEC(ipiv), KCMAT(b), CMAT(x)) {
    integer m = ar;
    integer n = ac;
    integer mrhs = br;
    integer nrhs = bc;

    REQUIRES(m==n && m==mrhs && m==ipivn,BAD_SIZE);
    integer* auxipiv = (integer*)malloc(n*sizeof(integer));
    int k;
    for (k=0; k<n; k++) {
        auxipiv[k] = (integer)ipivp[k];
    }
    integer res;
    memcpy(xp,bp,mrhs*nrhs*sizeof(doublecomplex));
    zgetrs_ ("N",&n,&nrhs,(doublecomplex*)ap,&m,auxipiv,xp,&mrhs,&res);
    CHECK(res,res);
    free(auxipiv);
    OK
}

//////////////////// Matrix Product /////////////////////////

void dgemm_(char *, char *, integer *, integer *, integer *,
           double *, const double *, integer *, const double *,
           integer *, double *, double *, integer *);

int multiplyR(int ta, int tb, KDMAT(a),KDMAT(b),DMAT(r)) {
    //REQUIRES(ac==br && ar==rr && bc==rc,BAD_SIZE);
    DEBUGMSG("dgemm_");
    CHECKNANR(a,"NaN multR Input\n")
    CHECKNANR(b,"NaN multR Input\n")
    integer m = ta?ac:ar;
    integer n = tb?br:bc;
    integer k = ta?ar:ac;
    integer lda = ar;
    integer ldb = br;
    integer ldc = rr;
    double alpha = 1;
    double beta = 0;
    dgemm_(ta?"T":"N",tb?"T":"N",&m,&n,&k,&alpha,ap,&lda,bp,&ldb,&beta,rp,&ldc);
    CHECKNANR(r,"NaN multR Output\n")
    OK
}

void zgemm_(char *, char *, integer *, integer *, integer *,
           doublecomplex *, const doublecomplex *, integer *, const doublecomplex *,
           integer *, doublecomplex *, doublecomplex *, integer *);

int multiplyC(int ta, int tb, KCMAT(a),KCMAT(b),CMAT(r)) {
    //REQUIRES(ac==br && ar==rr && bc==rc,BAD_SIZE);
    DEBUGMSG("zgemm_");
    CHECKNANC(a,"NaN multC Input\n")
    CHECKNANC(b,"NaN multC Input\n")
    integer m = ta?ac:ar;
    integer n = tb?br:bc;
    integer k = ta?ar:ac;
    integer lda = ar;
    integer ldb = br;
    integer ldc = rr;
    doublecomplex alpha = {1,0};
    doublecomplex beta = {0,0};
    zgemm_(ta?"T":"N",tb?"T":"N",&m,&n,&k,&alpha,
           ap,&lda,
           bp,&ldb,&beta,
           rp,&ldc);
    CHECKNANC(r,"NaN multC Output\n")
    OK
}

void sgemm_(char *, char *, integer *, integer *, integer *,
            float *, const float *, integer *, const float *,
           integer *, float *, float *, integer *);

int multiplyF(int ta, int tb, KFMAT(a),KFMAT(b),FMAT(r)) {
    //REQUIRES(ac==br && ar==rr && bc==rc,BAD_SIZE);
    DEBUGMSG("sgemm_");
    integer m = ta?ac:ar;
    integer n = tb?br:bc;
    integer k = ta?ar:ac;
    integer lda = ar;
    integer ldb = br;
    integer ldc = rr;
    float alpha = 1;
    float beta = 0;
    sgemm_(ta?"T":"N",tb?"T":"N",&m,&n,&k,&alpha,ap,&lda,bp,&ldb,&beta,rp,&ldc);
    OK
}

void cgemm_(char *, char *, integer *, integer *, integer *,
           complex *, const complex *, integer *, const complex *,
           integer *, complex *, complex *, integer *);

int multiplyQ(int ta, int tb, KQMAT(a),KQMAT(b),QMAT(r)) {
    //REQUIRES(ac==br && ar==rr && bc==rc,BAD_SIZE);
    DEBUGMSG("cgemm_");
    integer m = ta?ac:ar;
    integer n = tb?br:bc;
    integer k = ta?ar:ac;
    integer lda = ar;
    integer ldb = br;
    integer ldc = rr;
    complex alpha = {1,0};
    complex beta = {0,0};
    cgemm_(ta?"T":"N",tb?"T":"N",&m,&n,&k,&alpha,
           ap,&lda,
           bp,&ldb,&beta,
           rp,&ldc);
    OK
}

//////////////////// transpose /////////////////////////

int transF(KFMAT(x),FMAT(t)) {
    REQUIRES(xr==tc && xc==tr,BAD_SIZE);
    DEBUGMSG("transF");
    int i,j;
    for (i=0; i<tr; i++) {
        for (j=0; j<tc; j++) {
        tp[i*tc+j] = xp[j*xc+i];
        }
    }
    OK
}

int transR(KDMAT(x),DMAT(t)) {
    REQUIRES(xr==tc && xc==tr,BAD_SIZE);
    DEBUGMSG("transR");
    int i,j;
    for (i=0; i<tr; i++) {
        for (j=0; j<tc; j++) {
        tp[i*tc+j] = xp[j*xc+i];
        }
    }
    OK
}

int transQ(KQMAT(x),QMAT(t)) {
    REQUIRES(xr==tc && xc==tr,BAD_SIZE);
    DEBUGMSG("transQ");
    int i,j;
    for (i=0; i<tr; i++) {
        for (j=0; j<tc; j++) {
        tp[i*tc+j] = xp[j*xc+i];
        }
    }
    OK
}

int transC(KCMAT(x),CMAT(t)) {
    REQUIRES(xr==tc && xc==tr,BAD_SIZE);
    DEBUGMSG("transC");
    int i,j;
    for (i=0; i<tr; i++) {
        for (j=0; j<tc; j++) {
        tp[i*tc+j] = xp[j*xc+i];
        }
    }
    OK
}

int transP(KPMAT(x), PMAT(t)) {
    REQUIRES(xr==tc && xc==tr,BAD_SIZE);
    REQUIRES(xs==ts,NOCONVER);
    DEBUGMSG("transP");
    int i,j;
    for (i=0; i<tr; i++) {
        for (j=0; j<tc; j++) {
	  memcpy(tp+(i*tc+j)*xs,xp +(j*xc+i)*xs,xs);
        }
    }
    OK
}

//////////////////// constant /////////////////////////

int constantF(float * pval, FVEC(r)) {
    DEBUGMSG("constantF")
    int k;
    double val = *pval;
    for(k=0;k<rn;k++) {
        rp[k]=val;
    }
    OK
}

int constantR(double * pval, DVEC(r)) {
    DEBUGMSG("constantR")
    int k;
    double val = *pval;
    for(k=0;k<rn;k++) {
        rp[k]=val;
    }
    OK
}

int constantQ(complex* pval, QVEC(r)) {
    DEBUGMSG("constantQ")
    int k;
    complex val = *pval;
    for(k=0;k<rn;k++) {
        rp[k]=val;
    }
    OK
}

int constantC(doublecomplex* pval, CVEC(r)) {
    DEBUGMSG("constantC")
    int k;
    doublecomplex val = *pval;
    for(k=0;k<rn;k++) {
        rp[k]=val;
    }
    OK
}

int constantP(void* pval, PVEC(r)) {
    DEBUGMSG("constantP")
    int k;
    for(k=0;k<rn;k++) {
      memcpy(rp+k*rs,pval,rs);
    }
    OK
}

//////////////////// float-double conversion /////////////////////////

int float2double(FVEC(x),DVEC(y)) {
    DEBUGMSG("float2double")
    int k;
    for(k=0;k<xn;k++) {
        yp[k]=xp[k];
    }
    OK
}

int double2float(DVEC(x),FVEC(y)) {
    DEBUGMSG("double2float")
    int k;
    for(k=0;k<xn;k++) {
        yp[k]=xp[k];
    }
    OK
}

//////////////////// conjugate /////////////////////////

int conjugateQ(KQVEC(x),QVEC(t)) {
    REQUIRES(xn==tn,BAD_SIZE);
    DEBUGMSG("conjugateQ");
    int k;
    for(k=0;k<xn;k++) {
        tp[k].r =  xp[k].r;
        tp[k].i = -xp[k].i;
    }
    OK
}

int conjugateC(KCVEC(x),CVEC(t)) {
    REQUIRES(xn==tn,BAD_SIZE);
    DEBUGMSG("conjugateC");
    int k;
    for(k=0;k<xn;k++) {
        tp[k].r =  xp[k].r;
        tp[k].i = -xp[k].i;
    }
    OK
}

//////////////////// step /////////////////////////

int stepF(FVEC(x),FVEC(y)) {
    DEBUGMSG("stepF")
    int k;
    for(k=0;k<xn;k++) {
        yp[k]=xp[k]>0;
    }
    OK
}

int stepD(DVEC(x),DVEC(y)) {
    DEBUGMSG("stepD")
    int k;
    for(k=0;k<xn;k++) {
        yp[k]=xp[k]>0;
    }
    OK
}

//////////////////// cond /////////////////////////

int condF(FVEC(x),FVEC(y),FVEC(lt),FVEC(eq),FVEC(gt),FVEC(r)) {
    REQUIRES(xn==yn && xn==ltn && xn==eqn && xn==gtn && xn==rn ,BAD_SIZE);
    DEBUGMSG("condF")
    int k;
    for(k=0;k<xn;k++) {
        rp[k] = xp[k]<yp[k]?ltp[k]:(xp[k]>yp[k]?gtp[k]:eqp[k]);
    }
    OK
}

int condD(DVEC(x),DVEC(y),DVEC(lt),DVEC(eq),DVEC(gt),DVEC(r)) {
    REQUIRES(xn==yn && xn==ltn && xn==eqn && xn==gtn && xn==rn ,BAD_SIZE);
    DEBUGMSG("condD")
    int k;
    for(k=0;k<xn;k++) {
        rp[k] = xp[k]<yp[k]?ltp[k]:(xp[k]>yp[k]?gtp[k]:eqp[k]);
    }
    OK
}

