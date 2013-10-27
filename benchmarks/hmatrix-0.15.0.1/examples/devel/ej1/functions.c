/* assuming row order */

typedef struct { double r, i; } doublecomplex;

#define DVEC(A) int A##n, double*A##p
#define CVEC(A) int A##n, doublecomplex*A##p
#define DMAT(A) int A##r, int A##c, double*A##p
#define CMAT(A) int A##r, int A##c, doublecomplex*A##p

#define AT(M,row,col) (M##p[(row)*M##c + (col)])

/*-----------------------------------------------------*/

int c_scale_vector(double s, DVEC(x), DVEC(y)) {
    int k;
    for (k=0; k<=yn; k++) {
        yp[k] = s*xp[k];
    }
    return 0;
}

/*-----------------------------------------------------*/

int c_diag(DMAT(m),DVEC(y),DMAT(z)) {
    int i,j;
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
