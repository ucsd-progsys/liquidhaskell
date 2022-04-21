{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

-----------------------------------------------------------------------------
{- |
Module      :  Numeric.LinearAlgebra.Algorithms
Copyright   :  (c) Alberto Ruiz 2006-9
License     :  GPL-style

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

High level generic interface to common matrix computations.

Specific functions for particular base types can also be explicitly
imported from "Numeric.LinearAlgebra.LAPACK".

-}
-----------------------------------------------------------------------------

module Numeric.LinearAlgebra.Algorithms (
-- * Supported types
    Field(),
-- * Linear Systems
    linearSolve,
    luSolve,
    cholSolve,
    linearSolveLS,
    linearSolveSVD,
    inv, pinv,
    det, invlndet,
    rank, rcond,
-- * Matrix factorizations
-- ** Singular value decomposition
    svd,
    fullSVD,
    thinSVD,
    compactSVD,
    singularValues,
    leftSV, rightSV,
-- ** Eigensystems
    eig, eigSH, eigSH',
    eigenvalues, eigenvaluesSH, eigenvaluesSH',
    geigSH',
-- ** QR
    qr, rq,
-- ** Cholesky
    chol, cholSH, mbCholSH,
-- ** Hessenberg
    hess,
-- ** Schur
    schur,
-- ** LU
    lu, luPacked,
-- * Matrix functions
    expm,
    sqrtm,
    matFunc,
-- * Nullspace
    nullspacePrec,
    nullVector,
    nullspaceSVD,
    orth,
-- * Norms
    Normed(..), NormType(..),
    relativeError,
-- * Misc
    eps, peps, i,
-- * Util
    haussholder,
    unpackQR, unpackHess,
    pinvTol,
    ranksv
) where


import Data.Packed.Internal hiding ((//))
import Data.Packed.Matrix
import Numeric.LinearAlgebra.LAPACK as LAPACK
import Data.List(foldl1')
import Data.Array
import Numeric.ContainerBoot


{- | Class used to define generic linear algebra computations for both real and complex matrices. Only double precision is supported in this version (we can
transform single precision objects using 'single' and 'double').

-}
class (Product t,
       Convert t,
       Container Vector t,
       Container Matrix t,
       Normed Matrix t,
       Normed Vector t) => Field t where
    svd'         :: Matrix t -> (Matrix t, Vector Double, Matrix t)
    thinSVD'     :: Matrix t -> (Matrix t, Vector Double, Matrix t)
    sv'          :: Matrix t -> Vector Double
    luPacked'    :: Matrix t -> (Matrix t, [Int])
    luSolve'     :: (Matrix t, [Int]) -> Matrix t -> Matrix t
    linearSolve' :: Matrix t -> Matrix t -> Matrix t
    cholSolve'   :: Matrix t -> Matrix t -> Matrix t
    linearSolveSVD' :: Matrix t -> Matrix t -> Matrix t
    linearSolveLS'  :: Matrix t -> Matrix t -> Matrix t
    eig'         :: Matrix t -> (Vector (Complex Double), Matrix (Complex Double))
    eigSH''      :: Matrix t -> (Vector Double, Matrix t)
    eigOnly      :: Matrix t -> Vector (Complex Double)
    eigOnlySH    :: Matrix t -> Vector Double
    cholSH'      :: Matrix t -> Matrix t
    mbCholSH'    :: Matrix t -> Maybe (Matrix t)
    qr'          :: Matrix t -> (Matrix t, Matrix t)
    hess'        :: Matrix t -> (Matrix t, Matrix t)
    schur'       :: Matrix t -> (Matrix t, Matrix t)


instance Field Double where
    svd' = svdRd
    thinSVD' = thinSVDRd
    sv' = svR
    luPacked' = luR
    luSolve' (l_u,perm) = lusR l_u perm
    linearSolve' = linearSolveR                 -- (luSolve . luPacked) ??
    cholSolve' = cholSolveR
    linearSolveLS' = linearSolveLSR
    linearSolveSVD' = linearSolveSVDR Nothing
    eig' = eigR
    eigSH'' = eigS
    eigOnly = eigOnlyR
    eigOnlySH = eigOnlyS
    cholSH' = cholS
    mbCholSH' = mbCholS
    qr' = unpackQR . qrR
    hess' = unpackHess hessR
    schur' = schurR

instance Field (Complex Double) where
#ifdef NOZGESDD
    svd' = svdC
    thinSVD' = thinSVDC
#else
    svd' = svdCd
    thinSVD' = thinSVDCd
#endif
    sv' = svC
    luPacked' = luC
    luSolve' (l_u,perm) = lusC l_u perm
    linearSolve' = linearSolveC
    cholSolve' = cholSolveC
    linearSolveLS' = linearSolveLSC
    linearSolveSVD' = linearSolveSVDC Nothing
    eig' = eigC
    eigOnly = eigOnlyC
    eigSH'' = eigH
    eigOnlySH = eigOnlyH
    cholSH' = cholH
    mbCholSH' = mbCholH
    qr' = unpackQR . qrC
    hess' = unpackHess hessC
    schur' = schurC

--------------------------------------------------------------

square m = rows m == cols m

vertical m = rows m >= cols m

exactHermitian m = m `equal` ctrans m

--------------------------------------------------------------

-- | Full singular value decomposition.
svd :: Field t => Matrix t -> (Matrix t, Vector Double, Matrix t)
svd = {-# SCC "svd" #-} svd'

-- | A version of 'svd' which returns only the @min (rows m) (cols m)@ singular vectors of @m@.
--
-- If @(u,s,v) = thinSVD m@ then @m == u \<> diag s \<> trans v@.
thinSVD :: Field t => Matrix t -> (Matrix t, Vector Double, Matrix t)
thinSVD = {-# SCC "thinSVD" #-} thinSVD'

-- | Singular values only.
singularValues :: Field t => Matrix t -> Vector Double
singularValues = {-# SCC "singularValues" #-} sv'

-- | A version of 'svd' which returns an appropriate diagonal matrix with the singular values.
--
-- If @(u,d,v) = fullSVD m@ then @m == u \<> d \<> trans v@.
fullSVD :: Field t => Matrix t -> (Matrix t, Matrix Double, Matrix t)
fullSVD m = (u,d,v) where
    (u,s,v) = svd m
    d = diagRect 0 s r c
    r = rows m
    c = cols m

-- | Similar to 'thinSVD', returning only the nonzero singular values and the corresponding singular vectors.
compactSVD :: Field t  => Matrix t -> (Matrix t, Vector Double, Matrix t)
compactSVD m = (u', subVector 0 d s, v') where
    (u,s,v) = thinSVD m
    d = rankSVD (1*eps) m s `max` 1
    u' = takeColumns d u
    v' = takeColumns d v


-- | Singular values and all right singular vectors.
rightSV :: Field t => Matrix t -> (Vector Double, Matrix t)
rightSV m | vertical m = let (_,s,v) = thinSVD m in (s,v)
          | otherwise  = let (_,s,v) = svd m     in (s,v)

-- | Singular values and all left singular vectors.
leftSV :: Field t => Matrix t -> (Matrix t, Vector Double)
leftSV m  | vertical m = let (u,s,_) = svd m     in (u,s)
          | otherwise  = let (u,s,_) = thinSVD m in (u,s)


--------------------------------------------------------------

-- | Obtains the LU decomposition of a matrix in a compact data structure suitable for 'luSolve'.
luPacked :: Field t => Matrix t -> (Matrix t, [Int])
luPacked = {-# SCC "luPacked" #-} luPacked'

-- | Solution of a linear system (for several right hand sides) from the precomputed LU factorization obtained by 'luPacked'.
luSolve :: Field t => (Matrix t, [Int]) -> Matrix t -> Matrix t
luSolve = {-# SCC "luSolve" #-} luSolve'

-- | Solve a linear system (for square coefficient matrix and several right-hand sides) using the LU decomposition. For underconstrained or overconstrained systems use 'linearSolveLS' or 'linearSolveSVD'.
-- It is similar to 'luSolve' . 'luPacked', but @linearSolve@ raises an error if called on a singular system.
linearSolve :: Field t => Matrix t -> Matrix t -> Matrix t
linearSolve = {-# SCC "linearSolve" #-} linearSolve'

-- | Solve a symmetric or Hermitian positive definite linear system using a precomputed Cholesky decomposition obtained by 'chol'.
cholSolve :: Field t => Matrix t -> Matrix t -> Matrix t
cholSolve = {-# SCC "cholSolve" #-} cholSolve'

-- | Minimum norm solution of a general linear least squares problem Ax=B using the SVD. Admits rank-deficient systems but it is slower than 'linearSolveLS'. The effective rank of A is determined by treating as zero those singular valures which are less than 'eps' times the largest singular value.
linearSolveSVD :: Field t => Matrix t -> Matrix t -> Matrix t
linearSolveSVD = {-# SCC "linearSolveSVD" #-} linearSolveSVD'


-- | Least squared error solution of an overconstrained linear system, or the minimum norm solution of an underconstrained system. For rank-deficient systems use 'linearSolveSVD'.
linearSolveLS :: Field t => Matrix t -> Matrix t -> Matrix t
linearSolveLS = {-# SCC "linearSolveLS" #-} linearSolveLS'

--------------------------------------------------------------

-- | Eigenvalues and eigenvectors of a general square matrix.
--
-- If @(s,v) = eig m@ then @m \<> v == v \<> diag s@
eig :: Field t => Matrix t -> (Vector (Complex Double), Matrix (Complex Double))
eig = {-# SCC "eig" #-} eig'

-- | Eigenvalues of a general square matrix.
eigenvalues :: Field t => Matrix t -> Vector (Complex Double)
eigenvalues = {-# SCC "eigenvalues" #-} eigOnly

-- | Similar to 'eigSH' without checking that the input matrix is hermitian or symmetric. It works with the upper triangular part.
eigSH' :: Field t => Matrix t -> (Vector Double, Matrix t)
eigSH' = {-# SCC "eigSH'" #-} eigSH''

-- | Similar to 'eigenvaluesSH' without checking that the input matrix is hermitian or symmetric. It works with the upper triangular part.
eigenvaluesSH' :: Field t => Matrix t -> Vector Double
eigenvaluesSH' = {-# SCC "eigenvaluesSH'" #-} eigOnlySH

-- | Eigenvalues and Eigenvectors of a complex hermitian or real symmetric matrix.
--
-- If @(s,v) = eigSH m@ then @m == v \<> diag s \<> ctrans v@
eigSH :: Field t => Matrix t -> (Vector Double, Matrix t)
eigSH m | exactHermitian m = eigSH' m
        | otherwise = error "eigSH requires complex hermitian or real symmetric matrix"

-- | Eigenvalues of a complex hermitian or real symmetric matrix.
eigenvaluesSH :: Field t => Matrix t -> Vector Double
eigenvaluesSH m | exactHermitian m = eigenvaluesSH' m
                | otherwise = error "eigenvaluesSH requires complex hermitian or real symmetric matrix"

--------------------------------------------------------------

-- | QR factorization.
--
-- If @(q,r) = qr m@ then @m == q \<> r@, where q is unitary and r is upper triangular.
qr :: Field t => Matrix t -> (Matrix t, Matrix t)
qr = {-# SCC "qr" #-} qr'

-- | RQ factorization.
--
-- If @(r,q) = rq m@ then @m == r \<> q@, where q is unitary and r is upper triangular.
rq :: Field t => Matrix t -> (Matrix t, Matrix t)
rq m =  {-# SCC "rq" #-} (r,q) where
    (q',r') = qr $ trans $ rev1 m
    r = rev2 (trans r')
    q = rev2 (trans q')
    rev1 = flipud . fliprl
    rev2 = fliprl . flipud

-- | Hessenberg factorization.
--
-- If @(p,h) = hess m@ then @m == p \<> h \<> ctrans p@, where p is unitary
-- and h is in upper Hessenberg form (it has zero entries below the first subdiagonal).
hess        :: Field t => Matrix t -> (Matrix t, Matrix t)
hess = hess'

-- | Schur factorization.
--
-- If @(u,s) = schur m@ then @m == u \<> s \<> ctrans u@, where u is unitary
-- and s is a Shur matrix. A complex Schur matrix is upper triangular. A real Schur matrix is
-- upper triangular in 2x2 blocks.
--
-- \"Anything that the Jordan decomposition can do, the Schur decomposition
-- can do better!\" (Van Loan)
schur       :: Field t => Matrix t -> (Matrix t, Matrix t)
schur = schur'


-- | Similar to 'cholSH', but instead of an error (e.g., caused by a matrix not positive definite) it returns 'Nothing'.
mbCholSH :: Field t => Matrix t -> Maybe (Matrix t)
mbCholSH = {-# SCC "mbCholSH" #-} mbCholSH'

-- | Similar to 'chol', without checking that the input matrix is hermitian or symmetric. It works with the upper triangular part.
cholSH      :: Field t => Matrix t -> Matrix t
cholSH = {-# SCC "cholSH" #-} cholSH'

-- | Cholesky factorization of a positive definite hermitian or symmetric matrix.
--
-- If @c = chol m@ then @c@ is upper triangular and @m == ctrans c \<> c@.
chol :: Field t => Matrix t ->  Matrix t
chol m | exactHermitian m = cholSH m
       | otherwise = error "chol requires positive definite complex hermitian or real symmetric matrix"


-- | Joint computation of inverse and logarithm of determinant of a square matrix.
invlndet :: (Floating t, Field t)
         => Matrix t
         -> (Matrix t, (t, t)) -- ^ (inverse, (log abs det, sign or phase of det)) 
invlndet m | square m = (im,(ladm,sdm))
           | otherwise = error $ "invlndet of nonsquare "++ shSize m ++ " matrix"
  where
    lp@(lup,perm) = luPacked m
    s = signlp (rows m) perm
    dg = toList $ takeDiag $ lup
    ladm = sum $ map (log.abs) dg
    sdm = s* product (map signum dg)
    im = luSolve lp (ident (rows m))


-- | Determinant of a square matrix. To avoid possible overflow or underflow use 'invlndet'.
det :: Field t => Matrix t -> t
det m | square m = {-# SCC "det" #-} s * (product $ toList $ takeDiag $ lup)
      | otherwise = error $ "det of nonsquare "++ shSize m ++ " matrix"
    where (lup,perm) = luPacked m
          s = signlp (rows m) perm

-- | Explicit LU factorization of a general matrix.
--
-- If @(l,u,p,s) = lu m@ then @m == p \<> l \<> u@, where l is lower triangular,
-- u is upper triangular, p is a permutation matrix and s is the signature of the permutation.
lu :: Field t => Matrix t -> (Matrix t, Matrix t, Matrix t, t)
lu = luFact . luPacked

-- | Inverse of a square matrix. See also 'invlndet'.
inv :: Field t => Matrix t -> Matrix t
inv m | square m = m `linearSolve` ident (rows m)
      | otherwise = error $ "inv of nonsquare "++ shSize m ++ " matrix"

-- | Pseudoinverse of a general matrix.
pinv :: Field t => Matrix t -> Matrix t
pinv m = linearSolveSVD m (ident (rows m))

-- | Numeric rank of a matrix from the SVD decomposition.
rankSVD :: Element t
        => Double   -- ^ numeric zero (e.g. 1*'eps')
        -> Matrix t -- ^ input matrix m
        -> Vector Double -- ^ 'sv' of m
        -> Int      -- ^ rank of m
rankSVD teps m s = ranksv teps (max (rows m) (cols m)) (toList s)

-- | Numeric rank of a matrix from its singular values.
ranksv ::  Double   -- ^ numeric zero (e.g. 1*'eps')
        -> Int      -- ^ maximum dimension of the matrix
        -> [Double] -- ^ singular values
        -> Int      -- ^ rank of m
ranksv teps maxdim s = k where
    g = maximum s
    tol = fromIntegral maxdim * g * teps
    s' = filter (>tol) s
    k = if g > teps then length s' else 0

-- | The machine precision of a Double: @eps = 2.22044604925031e-16@ (the value used by GNU-Octave).
eps :: Double
eps =  2.22044604925031e-16


-- | 1 + 0.5*peps == 1,  1 + 0.6*peps /= 1
peps :: RealFloat x => x
peps = x where x = 2.0 ** fromIntegral (1 - floatDigits x)


-- | The imaginary unit: @i = 0.0 :+ 1.0@
i :: Complex Double
i = 0:+1

-----------------------------------------------------------------------

-- | The nullspace of a matrix from its SVD decomposition.
nullspaceSVD :: Field t
             => Either Double Int -- ^ Left \"numeric\" zero (eg. 1*'eps'),
                                  --   or Right \"theoretical\" matrix rank.
             -> Matrix t          -- ^ input matrix m
             -> (Vector Double, Matrix t) -- ^ 'rightSV' of m
             -> [Vector t]        -- ^ list of unitary vectors spanning the nullspace
nullspaceSVD hint a (s,v) = vs where
    tol = case hint of
        Left t -> t
        _      -> eps
    k = case hint of
        Right t -> t
        _       -> rankSVD tol a s
    vs = drop k $ toRows $ ctrans v


-- | The nullspace of a matrix. See also 'nullspaceSVD'.
nullspacePrec :: Field t
              => Double     -- ^ relative tolerance in 'eps' units (e.g., use 3 to get 3*'eps')
              -> Matrix t   -- ^ input matrix
              -> [Vector t] -- ^ list of unitary vectors spanning the nullspace
nullspacePrec t m = nullspaceSVD (Left (t*eps)) m (rightSV m)

-- | The nullspace of a matrix, assumed to be one-dimensional, with machine precision.
nullVector :: Field t => Matrix t -> Vector t
nullVector = last . nullspacePrec 1

orth :: Field t => Matrix t -> [Vector t]
-- ^ Return an orthonormal basis of the range space of a matrix
orth m = take r $ toColumns u
  where
    (u,s,_) = compactSVD m
    r = ranksv eps (max (rows m) (cols m)) (toList s)

------------------------------------------------------------------------

{-  Pseudoinverse of a real matrix with the desired tolerance, expressed as a
multiplicative factor of the default tolerance used by GNU-Octave (see 'pinv').

@\> let m = 'fromLists' [[1,0,    0]
                    ,[0,1,    0]
                    ,[0,0,1e-10]]
\  --
\> 'pinv' m 
1. 0.           0.
0. 1.           0.
0. 0. 10000000000.
\  --
\> pinvTol 1E8 m
1. 0. 0.
0. 1. 0.
0. 0. 1.@

-}
--pinvTol :: Double -> Matrix Double -> Matrix Double
pinvTol t m = v' `mXm` diag s' `mXm` trans u' where
    (u,s,v) = thinSVDRd m
    sl@(g:_) = toList s
    s' = fromList . map rec $ sl
    rec x = if x < g*tol then 1 else 1/x
    tol = (fromIntegral (max r c) * g * t * eps)
    r = rows m
    c = cols m
    d = dim s
    u' = takeColumns d u
    v' = takeColumns d v

---------------------------------------------------------------------

-- many thanks, quickcheck!

haussholder :: (Field a) => a -> Vector a -> Matrix a
haussholder tau v = ident (dim v) `sub` (tau `scale` (w `mXm` ctrans w))
    where w = asColumn v


zh k v = fromList $ replicate (k-1) 0 ++ (1:drop k xs)
              where xs = toList v

zt 0 v = v
zt k v = join [subVector 0 (dim v - k) v, konst 0 k]


unpackQR :: (Field t) => (Matrix t, Vector t) -> (Matrix t, Matrix t)
unpackQR (pq, tau) =  {-# SCC "unpackQR" #-} (q,r)
    where cs = toColumns pq
          m = rows pq
          n = cols pq
          mn = min m n
          r = fromColumns $ zipWith zt ([m-1, m-2 .. 1] ++ repeat 0) cs
          vs = zipWith zh [1..mn] cs
          hs = zipWith haussholder (toList tau) vs
          q = foldl1' mXm hs

unpackHess :: (Field t) => (Matrix t -> (Matrix t,Vector t)) -> Matrix t -> (Matrix t, Matrix t)
unpackHess hf m
    | rows m == 1 = ((1><1)[1],m)
    | otherwise = (uH . hf) m

uH (pq, tau) = (p,h)
    where cs = toColumns pq
          m = rows pq
          n = cols pq
          mn = min m n
          h = fromColumns $ zipWith zt ([m-2, m-3 .. 1] ++ repeat 0) cs
          vs = zipWith zh [2..mn] cs
          hs = zipWith haussholder (toList tau) vs
          p = foldl1' mXm hs

--------------------------------------------------------------------------

-- | Reciprocal of the 2-norm condition number of a matrix, computed from the singular values.
rcond :: Field t => Matrix t -> Double
rcond m = last s / head s
    where s = toList (singularValues m)

-- | Number of linearly independent rows or columns.
rank :: Field t => Matrix t -> Int
rank m = rankSVD eps m (singularValues m)

{-
expm' m = case diagonalize (complex m) of
    Just (l,v) -> v `mXm` diag (exp l) `mXm` inv v
    Nothing -> error "Sorry, expm not yet implemented for non-diagonalizable matrices"
  where exp = vectorMapC Exp
-}

diagonalize m = if rank v == n
                    then Just (l,v)
                    else Nothing
    where n = rows m
          (l,v) = if exactHermitian m
                    then let (l',v') = eigSH m in (real l', v')
                    else eig m

-- | Generic matrix functions for diagonalizable matrices. For instance:
--
-- @logm = matFunc log@
--
matFunc :: (Complex Double -> Complex Double) -> Matrix (Complex Double) -> Matrix (Complex Double)
matFunc f m = case diagonalize m of
    Just (l,v) -> v `mXm` diag (mapVector f l) `mXm` inv v
    Nothing -> error "Sorry, matFunc requires a diagonalizable matrix" 

--------------------------------------------------------------

golubeps :: Integer -> Integer -> Double
golubeps p q = a * fromIntegral b / fromIntegral c where
    a = 2^^(3-p-q)
    b = fact p * fact q
    c = fact (p+q) * fact (p+q+1)
    fact n = product [1..n]

epslist = [ (fromIntegral k, golubeps k k) | k <- [1..]]

geps delta = head [ k | (k,g) <- epslist, g<delta]


{- | Matrix exponential. It uses a direct translation of Algorithm 11.3.1 in Golub & Van Loan,
     based on a scaled Pade approximation.
-}
expm :: Field t => Matrix t -> Matrix t
expm = expGolub

expGolub :: ( Fractional t, Element t, Field t
            , Normed Matrix t
            , RealFrac (RealOf t)
            , Floating (RealOf t)
            ) => Matrix t -> Matrix t
expGolub m = iterate msq f !! j
    where j = max 0 $ floor $ logBase 2 $ pnorm Infinity m
          a = m */ fromIntegral ((2::Int)^j)
          q = geps eps -- 7 steps
          eye = ident (rows m)
          work (k,c,x,n,d) = (k',c',x',n',d')
              where k' = k+1
                    c' = c * fromIntegral (q-k+1) / fromIntegral ((2*q-k+1)*k)
                    x' = a <> x
                    n' = n |+| (c' .* x')
                    d' = d |+| (((-1)^k * c') .* x')
          (_,_,_,nf,df) = iterate work (1,1,eye,eye,eye) !! q
          f = linearSolve df nf
          msq x = x <> x

          (<>) = multiply
          v */ x = scale (recip x) v
          (.*) = scale
          (|+|) = add

--------------------------------------------------------------

{- | Matrix square root. Currently it uses a simple iterative algorithm described in Wikipedia.
It only works with invertible matrices that have a real solution. For diagonalizable matrices you can try @matFunc sqrt@.

@m = (2><2) [4,9
           ,0,4] :: Matrix Double@

@\>sqrtm m
(2><2)
 [ 2.0, 2.25
 , 0.0,  2.0 ]@
-}
sqrtm ::  Field t => Matrix t -> Matrix t
sqrtm = sqrtmInv

sqrtmInv x = fst $ fixedPoint $ iterate f (x, ident (rows x))
    where fixedPoint (a:b:rest) | pnorm PNorm1 (fst a |-| fst b) < peps   = a
                                | otherwise = fixedPoint (b:rest)
          fixedPoint _ = error "fixedpoint with impossible inputs"
          f (y,z) = (0.5 .* (y |+| inv z),
                     0.5 .* (inv y |+| z))
          (.*) = scale
          (|+|) = add
          (|-|) = sub

------------------------------------------------------------------

signlp r vals = foldl f 1 (zip [0..r-1] vals)
    where f s (a,b) | a /= b    = -s
                    | otherwise =  s

swap (arr,s) (a,b) | a /= b    = (arr // [(a, arr!b),(b,arr!a)],-s)
                   | otherwise = (arr,s)

fixPerm r vals = (fromColumns $ elems res, sign)
    where v = [0..r-1]
          s = toColumns (ident r)
          (res,sign) = foldl swap (listArray (0,r-1) s, 1) (zip v vals)

triang r c h v = (r><c) [el s t | s<-[0..r-1], t<-[0..c-1]]
    where el p q = if q-p>=h then v else 1 - v

luFact (l_u,perm) | r <= c    = (l ,u ,p, s)
                  | otherwise = (l',u',p, s)
  where
    r = rows l_u
    c = cols l_u
    tu = triang r c 0 1
    tl = triang r c 0 0
    l = takeColumns r (l_u |*| tl) |+| diagRect 0 (konst 1 r) r r
    u = l_u |*| tu
    (p,s) = fixPerm r perm
    l' = (l_u |*| tl) |+| diagRect 0 (konst 1 c) r c
    u' = takeRows c (l_u |*| tu)
    (|+|) = add
    (|*|) = mul

---------------------------------------------------------------------------

data NormType = Infinity | PNorm1 | PNorm2 | Frobenius

class (RealFloat (RealOf t)) => Normed c t where
    pnorm :: NormType -> c t -> RealOf t

instance Normed Vector Double where
    pnorm PNorm1    = norm1
    pnorm PNorm2    = norm2
    pnorm Infinity  = normInf
    pnorm Frobenius = norm2

instance Normed Vector (Complex Double) where
    pnorm PNorm1    = norm1
    pnorm PNorm2    = norm2
    pnorm Infinity  = normInf
    pnorm Frobenius = pnorm PNorm2

instance Normed Vector Float where
    pnorm PNorm1    = norm1
    pnorm PNorm2    = norm2
    pnorm Infinity  = normInf
    pnorm Frobenius = pnorm PNorm2

instance Normed Vector (Complex Float) where
    pnorm PNorm1    = norm1
    pnorm PNorm2    = norm2
    pnorm Infinity  = normInf
    pnorm Frobenius = pnorm PNorm2


instance Normed Matrix Double where
    pnorm PNorm1    = maximum . map (pnorm PNorm1) . toColumns
    pnorm PNorm2    = (@>0) . singularValues
    pnorm Infinity  = pnorm PNorm1 . trans
    pnorm Frobenius = pnorm PNorm2 . flatten

instance Normed Matrix (Complex Double) where
    pnorm PNorm1    = maximum . map (pnorm PNorm1) . toColumns
    pnorm PNorm2    = (@>0) . singularValues
    pnorm Infinity  = pnorm PNorm1 . trans
    pnorm Frobenius = pnorm PNorm2 . flatten

instance Normed Matrix Float where
    pnorm PNorm1    = maximum . map (pnorm PNorm1) . toColumns
    pnorm PNorm2    = realToFrac . (@>0) . singularValues . double
    pnorm Infinity  = pnorm PNorm1 . trans
    pnorm Frobenius = pnorm PNorm2 . flatten

instance Normed Matrix (Complex Float) where
    pnorm PNorm1    = maximum . map (pnorm PNorm1) . toColumns
    pnorm PNorm2    = realToFrac . (@>0) . singularValues . double
    pnorm Infinity  = pnorm PNorm1 . trans
    pnorm Frobenius = pnorm PNorm2 . flatten

-- | Approximate number of common digits in the maximum element.
relativeError :: (Normed c t, Container c t) => c t -> c t -> Int
relativeError x y = dig (norm (x `sub` y) / norm x)
    where norm = pnorm Infinity
          dig r = round $ -logBase 10 (realToFrac r :: Double)

----------------------------------------------------------------------

-- | Generalized symmetric positive definite eigensystem Av = lBv,
-- for A and B symmetric, B positive definite (conditions not checked).
geigSH' :: Field t
        => Matrix t -- ^ A
        -> Matrix t -- ^ B
        -> (Vector Double, Matrix t)
geigSH' a b = (l,v')
  where
    u = cholSH b
    iu = inv u
    c = ctrans iu <> a <> iu
    (l,v) = eigSH' c
    v' = iu <> v
    (<>) = mXm

