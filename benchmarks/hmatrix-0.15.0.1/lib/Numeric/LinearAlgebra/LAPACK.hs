-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.LinearAlgebra.LAPACK
-- Copyright   :  (c) Alberto Ruiz 2006-7
-- License     :  GPL-style
-- 
-- Maintainer  :  Alberto Ruiz (aruiz at um dot es)
-- Stability   :  provisional
-- Portability :  portable (uses FFI)
--
-- Functional interface to selected LAPACK functions (<http://www.netlib.org/lapack>).
--
-----------------------------------------------------------------------------

module Numeric.LinearAlgebra.LAPACK (
    -- * Matrix product
    multiplyR, multiplyC, multiplyF, multiplyQ,
    -- * Linear systems
    linearSolveR, linearSolveC,
    lusR, lusC,
    cholSolveR, cholSolveC,
    linearSolveLSR, linearSolveLSC,
    linearSolveSVDR, linearSolveSVDC,
    -- * SVD
    svR, svRd, svC, svCd,
    svdR, svdRd, svdC, svdCd,
    thinSVDR, thinSVDRd, thinSVDC, thinSVDCd,
    rightSVR, rightSVC, leftSVR, leftSVC,
    -- * Eigensystems
    eigR, eigC, eigS, eigS', eigH, eigH',
    eigOnlyR, eigOnlyC, eigOnlyS, eigOnlyH,
    -- * LU
    luR, luC,
    -- * Cholesky
    cholS, cholH, mbCholS, mbCholH,
    -- * QR
    qrR, qrC,
    -- * Hessenberg
    hessR, hessC,
    -- * Schur
    schurR, schurC
) where

import Data.Packed.Internal
import Data.Packed.Matrix
import Numeric.Conversion
import Numeric.GSL.Vector(vectorMapValR, FunCodeSV(Scale))

import Foreign.Ptr(nullPtr)
import Foreign.C.Types
import Control.Monad(when)
import System.IO.Unsafe(unsafePerformIO)

-----------------------------------------------------------------------------------

foreign import ccall unsafe "multiplyR" dgemmc :: CInt -> CInt -> TMMM
foreign import ccall unsafe "multiplyC" zgemmc :: CInt -> CInt -> TCMCMCM
foreign import ccall unsafe "multiplyF" sgemmc :: CInt -> CInt -> TFMFMFM
foreign import ccall unsafe "multiplyQ" cgemmc :: CInt -> CInt -> TQMQMQM

isT Matrix{order = ColumnMajor} = 0
isT Matrix{order = RowMajor} = 1

tt x@Matrix{order = ColumnMajor} = x
tt x@Matrix{order = RowMajor} = trans x

multiplyAux f st a b = unsafePerformIO $ do
    when (cols a /= rows b) $ error $ "inconsistent dimensions in matrix product "++
                                       show (rows a,cols a) ++ " x " ++ show (rows b, cols b)
    s <- createMatrix ColumnMajor (rows a) (cols b)
    app3 (f (isT a) (isT b)) mat (tt a) mat (tt b) mat s st
    return s

-- | Matrix product based on BLAS's /dgemm/.
multiplyR :: Matrix Double -> Matrix Double -> Matrix Double
multiplyR a b = {-# SCC "multiplyR" #-} multiplyAux dgemmc "dgemmc" a b

-- | Matrix product based on BLAS's /zgemm/.
multiplyC :: Matrix (Complex Double) -> Matrix (Complex Double) -> Matrix (Complex Double)
multiplyC a b = multiplyAux zgemmc "zgemmc" a b

-- | Matrix product based on BLAS's /sgemm/.
multiplyF :: Matrix Float -> Matrix Float -> Matrix Float
multiplyF a b = multiplyAux sgemmc "sgemmc" a b

-- | Matrix product based on BLAS's /cgemm/.
multiplyQ :: Matrix (Complex Float) -> Matrix (Complex Float) -> Matrix (Complex Float)
multiplyQ a b = multiplyAux cgemmc "cgemmc" a b

-----------------------------------------------------------------------------
foreign import ccall unsafe "svd_l_R" dgesvd :: TMMVM
foreign import ccall unsafe "svd_l_C" zgesvd :: TCMCMVCM
foreign import ccall unsafe "svd_l_Rdd" dgesdd :: TMMVM
foreign import ccall unsafe "svd_l_Cdd" zgesdd :: TCMCMVCM

-- | Full SVD of a real matrix using LAPACK's /dgesvd/.
svdR :: Matrix Double -> (Matrix Double, Vector Double, Matrix Double)
svdR = svdAux dgesvd "svdR" . fmat

-- | Full SVD of a real matrix using LAPACK's /dgesdd/.
svdRd :: Matrix Double -> (Matrix Double, Vector Double, Matrix Double)
svdRd = svdAux dgesdd "svdRdd" . fmat

-- | Full SVD of a complex matrix using LAPACK's /zgesvd/.
svdC :: Matrix (Complex Double) -> (Matrix (Complex Double), Vector Double, Matrix (Complex Double))
svdC = svdAux zgesvd "svdC" . fmat

-- | Full SVD of a complex matrix using LAPACK's /zgesdd/.
svdCd :: Matrix (Complex Double) -> (Matrix (Complex Double), Vector Double, Matrix (Complex Double))
svdCd = svdAux zgesdd "svdCdd" . fmat

svdAux f st x = unsafePerformIO $ do
    u <- createMatrix ColumnMajor r r
    s <- createVector (min r c)
    v <- createMatrix ColumnMajor c c
    app4 f mat x mat u vec s mat v st
    return (u,s,trans v)
  where r = rows x
        c = cols x


-- | Thin SVD of a real matrix, using LAPACK's /dgesvd/ with jobu == jobvt == \'S\'.
thinSVDR :: Matrix Double -> (Matrix Double, Vector Double, Matrix Double)
thinSVDR = thinSVDAux dgesvd "thinSVDR" . fmat

-- | Thin SVD of a complex matrix, using LAPACK's /zgesvd/ with jobu == jobvt == \'S\'.
thinSVDC :: Matrix (Complex Double) -> (Matrix (Complex Double), Vector Double, Matrix (Complex Double))
thinSVDC = thinSVDAux zgesvd "thinSVDC" . fmat

-- | Thin SVD of a real matrix, using LAPACK's /dgesdd/ with jobz == \'S\'.
thinSVDRd :: Matrix Double -> (Matrix Double, Vector Double, Matrix Double)
thinSVDRd = thinSVDAux dgesdd "thinSVDRdd" . fmat

-- | Thin SVD of a complex matrix, using LAPACK's /zgesdd/ with jobz == \'S\'.
thinSVDCd :: Matrix (Complex Double) -> (Matrix (Complex Double), Vector Double, Matrix (Complex Double))
thinSVDCd = thinSVDAux zgesdd "thinSVDCdd" . fmat

thinSVDAux f st x = unsafePerformIO $ do
    u <- createMatrix ColumnMajor r q
    s <- createVector q
    v <- createMatrix ColumnMajor q c
    app4 f mat x mat u vec s mat v st
    return (u,s,trans v)
  where r = rows x
        c = cols x
        q = min r c


-- | Singular values of a real matrix, using LAPACK's /dgesvd/ with jobu == jobvt == \'N\'.
svR :: Matrix Double -> Vector Double
svR = svAux dgesvd "svR" . fmat

-- | Singular values of a complex matrix, using LAPACK's /zgesvd/ with jobu == jobvt == \'N\'.
svC :: Matrix (Complex Double) -> Vector Double
svC = svAux zgesvd "svC" . fmat

-- | Singular values of a real matrix, using LAPACK's /dgesdd/ with jobz == \'N\'.
svRd :: Matrix Double -> Vector Double
svRd = svAux dgesdd "svRd" . fmat

-- | Singular values of a complex matrix, using LAPACK's /zgesdd/ with jobz == \'N\'.
svCd :: Matrix (Complex Double) -> Vector Double
svCd = svAux zgesdd "svCd" . fmat

svAux f st x = unsafePerformIO $ do
    s <- createVector q
    app2 g mat x vec s st
    return s
  where r = rows x
        c = cols x
        q = min r c
        g ra ca pa nb pb = f ra ca pa 0 0 nullPtr nb pb 0 0 nullPtr


-- | Singular values and all right singular vectors of a real matrix, using LAPACK's /dgesvd/ with jobu == \'N\' and jobvt == \'A\'.
rightSVR :: Matrix Double -> (Vector Double, Matrix Double)
rightSVR = rightSVAux dgesvd "rightSVR" . fmat

-- | Singular values and all right singular vectors of a complex matrix, using LAPACK's /zgesvd/ with jobu == \'N\' and jobvt == \'A\'.
rightSVC :: Matrix (Complex Double) -> (Vector Double, Matrix (Complex Double))
rightSVC = rightSVAux zgesvd "rightSVC" . fmat

rightSVAux f st x = unsafePerformIO $ do
    s <- createVector q
    v <- createMatrix ColumnMajor c c
    app3 g mat x vec s mat v st
    return (s,trans v)
  where r = rows x
        c = cols x
        q = min r c
        g ra ca pa = f ra ca pa 0 0 nullPtr


-- | Singular values and all left singular vectors of a real matrix, using LAPACK's /dgesvd/  with jobu == \'A\' and jobvt == \'N\'.
leftSVR :: Matrix Double -> (Matrix Double, Vector Double)
leftSVR = leftSVAux dgesvd "leftSVR" . fmat

-- | Singular values and all left singular vectors of a complex matrix, using LAPACK's /zgesvd/ with jobu == \'A\' and jobvt == \'N\'.
leftSVC :: Matrix (Complex Double) -> (Matrix (Complex Double), Vector Double)
leftSVC = leftSVAux zgesvd "leftSVC" . fmat

leftSVAux f st x = unsafePerformIO $ do
    u <- createMatrix ColumnMajor r r
    s <- createVector q
    app3 g mat x mat u vec s st
    return (u,s)
  where r = rows x
        c = cols x
        q = min r c
        g ra ca pa ru cu pu nb pb = f ra ca pa ru cu pu nb pb 0 0 nullPtr

-----------------------------------------------------------------------------

foreign import ccall unsafe "eig_l_R" dgeev :: TMMCVM
foreign import ccall unsafe "eig_l_C" zgeev :: TCMCMCVCM
foreign import ccall unsafe "eig_l_S" dsyev :: CInt -> TMVM
foreign import ccall unsafe "eig_l_H" zheev :: CInt -> TCMVCM

eigAux f st m = unsafePerformIO $ do
        l <- createVector r
        v <- createMatrix ColumnMajor r r
        app3 g mat m vec l mat v st
        return (l,v)
  where r = rows m
        g ra ca pa = f ra ca pa 0 0 nullPtr


-- | Eigenvalues and right eigenvectors of a general complex matrix, using LAPACK's /zgeev/.
-- The eigenvectors are the columns of v. The eigenvalues are not sorted.
eigC :: Matrix (Complex Double) -> (Vector (Complex Double), Matrix (Complex Double))
eigC = eigAux zgeev "eigC" . fmat

eigOnlyAux f st m = unsafePerformIO $ do
        l <- createVector r
        app2 g mat m vec l st
        return l
  where r = rows m
        g ra ca pa nl pl = f ra ca pa 0 0 nullPtr nl pl 0 0 nullPtr

-- | Eigenvalues of a general complex matrix, using LAPACK's /zgeev/ with jobz == \'N\'.
-- The eigenvalues are not sorted.
eigOnlyC :: Matrix (Complex Double) -> Vector (Complex Double)
eigOnlyC = eigOnlyAux zgeev "eigOnlyC" . fmat

-- | Eigenvalues and right eigenvectors of a general real matrix, using LAPACK's /dgeev/.
-- The eigenvectors are the columns of v. The eigenvalues are not sorted.
eigR :: Matrix Double -> (Vector (Complex Double), Matrix (Complex Double))
eigR m = (s', v'')
    where (s,v) = eigRaux (fmat m)
          s' = fixeig1 s
          v' = toRows $ trans v
          v'' = fromColumns $ fixeig (toList s') v'

eigRaux :: Matrix Double -> (Vector (Complex Double), Matrix Double)
eigRaux m = unsafePerformIO $ do
        l <- createVector r
        v <- createMatrix ColumnMajor r r
        app3 g mat m vec l mat v "eigR"
        return (l,v)
  where r = rows m
        g ra ca pa = dgeev ra ca pa 0 0 nullPtr

fixeig1 s = toComplex' (subVector 0 r (asReal s), subVector r r (asReal s))
    where r = dim s

fixeig  []  _ =  []
fixeig [_] [v] = [comp' v]
fixeig ((r1:+i1):(r2:+i2):r) (v1:v2:vs)
    | r1 == r2 && i1 == (-i2) = toComplex' (v1,v2) : toComplex' (v1,scale (-1) v2) : fixeig r vs
    | otherwise = comp' v1 : fixeig ((r2:+i2):r) (v2:vs)
  where scale = vectorMapValR Scale
fixeig _ _ = error "fixeig with impossible inputs"


-- | Eigenvalues of a general real matrix, using LAPACK's /dgeev/ with jobz == \'N\'.
-- The eigenvalues are not sorted.
eigOnlyR :: Matrix Double -> Vector (Complex Double)
eigOnlyR = fixeig1 . eigOnlyAux dgeev "eigOnlyR" . fmat


-----------------------------------------------------------------------------

eigSHAux f st m = unsafePerformIO $ do
        l <- createVector r
        v <- createMatrix ColumnMajor r r
        app3 f mat m vec l mat v st
        return (l,v)
  where r = rows m

-- | Eigenvalues and right eigenvectors of a symmetric real matrix, using LAPACK's /dsyev/.
-- The eigenvectors are the columns of v.
-- The eigenvalues are sorted in descending order (use 'eigS'' for ascending order).
eigS :: Matrix Double -> (Vector Double, Matrix Double)
eigS m = (s', fliprl v)
    where (s,v) = eigS' (fmat m)
          s' = fromList . reverse . toList $  s

-- | 'eigS' in ascending order
eigS' :: Matrix Double -> (Vector Double, Matrix Double)
eigS' = eigSHAux (dsyev 1) "eigS'" . fmat

-- | Eigenvalues and right eigenvectors of a hermitian complex matrix, using LAPACK's /zheev/.
-- The eigenvectors are the columns of v.
-- The eigenvalues are sorted in descending order (use 'eigH'' for ascending order).
eigH :: Matrix (Complex Double) -> (Vector Double, Matrix (Complex Double))
eigH m = (s', fliprl v)
    where (s,v) = eigH' (fmat m)
          s' = fromList . reverse . toList $  s

-- | 'eigH' in ascending order
eigH' :: Matrix (Complex Double) -> (Vector Double, Matrix (Complex Double))
eigH' = eigSHAux (zheev 1) "eigH'" . fmat


-- | Eigenvalues of a symmetric real matrix, using LAPACK's /dsyev/ with jobz == \'N\'.
-- The eigenvalues are sorted in descending order.
eigOnlyS :: Matrix Double -> Vector Double
eigOnlyS = vrev . fst. eigSHAux (dsyev 0) "eigS'" . fmat

-- | Eigenvalues of a hermitian complex matrix, using LAPACK's /zheev/ with jobz == \'N\'.
-- The eigenvalues are sorted in descending order.
eigOnlyH :: Matrix (Complex Double) -> Vector Double
eigOnlyH = vrev . fst. eigSHAux (zheev 1) "eigH'" . fmat

vrev = flatten . flipud . reshape 1

-----------------------------------------------------------------------------
foreign import ccall unsafe "linearSolveR_l" dgesv :: TMMM
foreign import ccall unsafe "linearSolveC_l" zgesv :: TCMCMCM
foreign import ccall unsafe "cholSolveR_l" dpotrs :: TMMM
foreign import ccall unsafe "cholSolveC_l" zpotrs :: TCMCMCM

linearSolveSQAux f st a b
    | n1==n2 && n1==r = unsafePerformIO $ do
        s <- createMatrix ColumnMajor r c
        app3 f mat a mat b mat s st
        return s
    | otherwise = error $ st ++ " of nonsquare matrix"
  where n1 = rows a
        n2 = cols a
        r  = rows b
        c  = cols b

-- | Solve a real linear system (for square coefficient matrix and several right-hand sides) using the LU decomposition, based on LAPACK's /dgesv/. For underconstrained or overconstrained systems use 'linearSolveLSR' or 'linearSolveSVDR'. See also 'lusR'.
linearSolveR :: Matrix Double -> Matrix Double -> Matrix Double
linearSolveR a b = linearSolveSQAux dgesv "linearSolveR" (fmat a) (fmat b)

-- | Solve a complex linear system (for square coefficient matrix and several right-hand sides) using the LU decomposition, based on LAPACK's /zgesv/. For underconstrained or overconstrained systems use 'linearSolveLSC' or 'linearSolveSVDC'. See also 'lusC'.
linearSolveC :: Matrix (Complex Double) -> Matrix (Complex Double) -> Matrix (Complex Double)
linearSolveC a b = linearSolveSQAux zgesv "linearSolveC" (fmat a) (fmat b)


-- | Solves a symmetric positive definite system of linear equations using a precomputed Cholesky factorization obtained by 'cholS'.
cholSolveR :: Matrix Double -> Matrix Double -> Matrix Double
cholSolveR a b = linearSolveSQAux dpotrs "cholSolveR" (fmat a) (fmat b)

-- | Solves a Hermitian positive definite system of linear equations using a precomputed Cholesky factorization obtained by 'cholH'.
cholSolveC :: Matrix (Complex Double) -> Matrix (Complex Double) -> Matrix (Complex Double)
cholSolveC a b = linearSolveSQAux zpotrs "cholSolveC" (fmat a) (fmat b)

-----------------------------------------------------------------------------------
foreign import ccall unsafe "linearSolveLSR_l" dgels :: TMMM
foreign import ccall unsafe "linearSolveLSC_l" zgels :: TCMCMCM
foreign import ccall unsafe "linearSolveSVDR_l" dgelss :: Double -> TMMM
foreign import ccall unsafe "linearSolveSVDC_l" zgelss :: Double -> TCMCMCM

linearSolveAux f st a b = unsafePerformIO $ do
    r <- createMatrix ColumnMajor (max m n) nrhs
    app3 f mat a mat b mat r st
    return r
  where m = rows a
        n = cols a
        nrhs = cols b

-- | Least squared error solution of an overconstrained real linear system, or the minimum norm solution of an underconstrained system, using LAPACK's /dgels/. For rank-deficient systems use 'linearSolveSVDR'.
linearSolveLSR :: Matrix Double -> Matrix Double -> Matrix Double
linearSolveLSR a b = subMatrix (0,0) (cols a, cols b) $
                     linearSolveAux dgels "linearSolverLSR" (fmat a) (fmat b)

-- | Least squared error solution of an overconstrained complex linear system, or the minimum norm solution of an underconstrained system, using LAPACK's /zgels/. For rank-deficient systems use 'linearSolveSVDC'.
linearSolveLSC :: Matrix (Complex Double) -> Matrix (Complex Double) -> Matrix (Complex Double)
linearSolveLSC a b = subMatrix (0,0) (cols a, cols b) $
                     linearSolveAux zgels "linearSolveLSC" (fmat a) (fmat b)

-- | Minimum norm solution of a general real linear least squares problem Ax=B using the SVD, based on LAPACK's /dgelss/. Admits rank-deficient systems but it is slower than 'linearSolveLSR'. The effective rank of A is determined by treating as zero those singular valures which are less than rcond times the largest singular value. If rcond == Nothing machine precision is used.
linearSolveSVDR :: Maybe Double   -- ^ rcond
                -> Matrix Double  -- ^ coefficient matrix
                -> Matrix Double  -- ^ right hand sides (as columns)
                -> Matrix Double  -- ^ solution vectors (as columns)
linearSolveSVDR (Just rcond) a b = subMatrix (0,0) (cols a, cols b) $
                                   linearSolveAux (dgelss rcond) "linearSolveSVDR" (fmat a) (fmat b)
linearSolveSVDR Nothing a b = linearSolveSVDR (Just (-1)) (fmat a) (fmat b)

-- | Minimum norm solution of a general complex linear least squares problem Ax=B using the SVD, based on LAPACK's /zgelss/. Admits rank-deficient systems but it is slower than 'linearSolveLSC'. The effective rank of A is determined by treating as zero those singular valures which are less than rcond times the largest singular value. If rcond == Nothing machine precision is used.
linearSolveSVDC :: Maybe Double            -- ^ rcond
                -> Matrix (Complex Double) -- ^ coefficient matrix
                -> Matrix (Complex Double) -- ^ right hand sides (as columns)
                -> Matrix (Complex Double) -- ^ solution vectors (as columns)
linearSolveSVDC (Just rcond) a b = subMatrix (0,0) (cols a, cols b) $
                                   linearSolveAux (zgelss rcond) "linearSolveSVDC" (fmat a) (fmat b)
linearSolveSVDC Nothing a b = linearSolveSVDC (Just (-1)) (fmat a) (fmat b)

-----------------------------------------------------------------------------------
foreign import ccall unsafe "chol_l_H" zpotrf :: TCMCM
foreign import ccall unsafe "chol_l_S" dpotrf :: TMM

cholAux f st a = do
    r <- createMatrix ColumnMajor n n
    app2 f mat a mat r st
    return r
  where n = rows a

-- | Cholesky factorization of a complex Hermitian positive definite matrix, using LAPACK's /zpotrf/.
cholH :: Matrix (Complex Double) -> Matrix (Complex Double)
cholH = unsafePerformIO . cholAux zpotrf "cholH" . fmat

-- | Cholesky factorization of a real symmetric positive definite matrix, using LAPACK's /dpotrf/.
cholS :: Matrix Double -> Matrix Double
cholS =  unsafePerformIO . cholAux dpotrf "cholS" . fmat

-- | Cholesky factorization of a complex Hermitian positive definite matrix, using LAPACK's /zpotrf/ ('Maybe' version).
mbCholH :: Matrix (Complex Double) -> Maybe (Matrix (Complex Double))
mbCholH = unsafePerformIO . mbCatch . cholAux zpotrf "cholH" . fmat

-- | Cholesky factorization of a real symmetric positive definite matrix, using LAPACK's /dpotrf/  ('Maybe' version).
mbCholS :: Matrix Double -> Maybe (Matrix Double)
mbCholS =  unsafePerformIO . mbCatch . cholAux dpotrf "cholS" . fmat

-----------------------------------------------------------------------------------
foreign import ccall unsafe "qr_l_R" dgeqr2 :: TMVM
foreign import ccall unsafe "qr_l_C" zgeqr2 :: TCMCVCM

-- | QR factorization of a real matrix, using LAPACK's /dgeqr2/.
qrR :: Matrix Double -> (Matrix Double, Vector Double)
qrR = qrAux dgeqr2 "qrR" . fmat

-- | QR factorization of a complex matrix, using LAPACK's /zgeqr2/.
qrC :: Matrix (Complex Double) -> (Matrix (Complex Double), Vector (Complex Double))
qrC = qrAux zgeqr2 "qrC" . fmat

qrAux f st a = unsafePerformIO $ do
    r <- createMatrix ColumnMajor m n
    tau <- createVector mn
    app3 f mat a vec tau mat r st
    return (r,tau)
  where m = rows a
        n = cols a
        mn = min m n

-----------------------------------------------------------------------------------
foreign import ccall unsafe "hess_l_R" dgehrd :: TMVM
foreign import ccall unsafe "hess_l_C" zgehrd :: TCMCVCM

-- | Hessenberg factorization of a square real matrix, using LAPACK's /dgehrd/.
hessR :: Matrix Double -> (Matrix Double, Vector Double)
hessR = hessAux dgehrd "hessR" . fmat

-- | Hessenberg factorization of a square complex matrix, using LAPACK's /zgehrd/.
hessC :: Matrix (Complex Double) -> (Matrix (Complex Double), Vector (Complex Double))
hessC = hessAux zgehrd "hessC" . fmat

hessAux f st a = unsafePerformIO $ do
    r <- createMatrix ColumnMajor m n
    tau <- createVector (mn-1)
    app3 f mat a vec tau mat r st
    return (r,tau)
  where m = rows a
        n = cols a
        mn = min m n

-----------------------------------------------------------------------------------
foreign import ccall unsafe "schur_l_R" dgees :: TMMM
foreign import ccall unsafe "schur_l_C" zgees :: TCMCMCM

-- | Schur factorization of a square real matrix, using LAPACK's /dgees/.
schurR :: Matrix Double -> (Matrix Double, Matrix Double)
schurR = schurAux dgees "schurR" . fmat

-- | Schur factorization of a square complex matrix, using LAPACK's /zgees/.
schurC :: Matrix (Complex Double) -> (Matrix (Complex Double), Matrix (Complex Double))
schurC = schurAux zgees "schurC" . fmat

schurAux f st a = unsafePerformIO $ do
    u <- createMatrix ColumnMajor n n
    s <- createMatrix ColumnMajor n n
    app3 f mat a mat u mat s st
    return (u,s)
  where n = rows a

-----------------------------------------------------------------------------------
foreign import ccall unsafe "lu_l_R" dgetrf :: TMVM
foreign import ccall unsafe "lu_l_C" zgetrf :: TCMVCM

-- | LU factorization of a general real matrix, using LAPACK's /dgetrf/.
luR :: Matrix Double -> (Matrix Double, [Int])
luR = luAux dgetrf "luR" . fmat

-- | LU factorization of a general complex matrix, using LAPACK's /zgetrf/.
luC :: Matrix (Complex Double) -> (Matrix (Complex Double), [Int])
luC = luAux zgetrf "luC" . fmat

luAux f st a = unsafePerformIO $ do
    lu <- createMatrix ColumnMajor n m
    piv <- createVector (min n m)
    app3 f mat a vec piv mat lu st
    return (lu, map (pred.round) (toList piv))
  where n = rows a
        m = cols a

-----------------------------------------------------------------------------------
type TW a = CInt -> PD -> a
type TQ a = CInt -> CInt -> PC -> a

foreign import ccall unsafe "luS_l_R" dgetrs :: TMVMM
foreign import ccall unsafe "luS_l_C" zgetrs :: TQ (TW (TQ (TQ (IO CInt))))

-- | Solve a real linear system from a precomputed LU decomposition ('luR'), using LAPACK's /dgetrs/.
lusR :: Matrix Double -> [Int] -> Matrix Double -> Matrix Double
lusR a piv b = lusAux dgetrs "lusR" (fmat a) piv (fmat b)

-- | Solve a real linear system from a precomputed LU decomposition ('luC'), using LAPACK's /zgetrs/.
lusC :: Matrix (Complex Double) -> [Int] -> Matrix (Complex Double) -> Matrix (Complex Double)
lusC a piv b = lusAux zgetrs "lusC" (fmat a) piv (fmat b)

lusAux f st a piv b
    | n1==n2 && n2==n =unsafePerformIO $ do
         x <- createMatrix ColumnMajor n m
         app4 f mat a vec piv' mat b mat x st
         return x
    | otherwise = error $ st ++ " on LU factorization of nonsquare matrix"
  where n1 = rows a
        n2 = cols a
        n = rows b
        m = cols b
        piv' = fromList (map (fromIntegral.succ) piv) :: Vector Double

