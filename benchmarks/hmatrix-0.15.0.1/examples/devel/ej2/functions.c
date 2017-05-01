/*  general element order   */

typedef struct { double r, i; } doublecomplex;

#define DVEC(A) int A##n, double*A##p
#define CVEC(A) int A##n, doublecomplex*A##p
#define DMAT(A) int A##r, int A##c, double*A##p
#define CMAT(A) int A##r, int A##c, doublecomplex*A##p

#define AT(M,r,c) (M##p[(r)*sr+(c)*sc])

int c_diag(int ro, DMAT(m),DVEC(y),DMAT(z)) {
    int i,j,sr,sc;
    if (ro==1) { sr = mc; sc = 1;} else { sr = 1; sc = mr;}
    for (j=0; j<yn; j++) {
        yp[j] = AT(m,j,j);
    }
    for (i=0; i<mr; i++) {
        for (j=0; j<mc; j++) {
            AT(z,i,j) = i==j?yp[i]:0;
        }
    }
    return 0;
}
