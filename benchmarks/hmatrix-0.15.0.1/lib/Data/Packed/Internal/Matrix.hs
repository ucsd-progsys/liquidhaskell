{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE BangPatterns             #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.Internal.Matrix
-- Copyright   :  (c) Alberto Ruiz 2007
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable (uses FFI)
--
-- Internal matrix representation
--
-----------------------------------------------------------------------------
-- #hide

module Data.Packed.Internal.Matrix(
    Matrix(..), rows, cols, cdat, fdat,
    MatrixOrder(..), orderOf,
    createMatrix, mat,
    cmat, fmat,
    toLists, flatten, reshape,
    Element(..),
    trans,
    fromRows, toRows, fromColumns, toColumns,
    matrixFromVector,
    subMatrix,
    liftMatrix, liftMatrix2,
    (@@>), atM',
    saveMatrix,
    singleton,
    size, shSize, conformVs, conformMs, conformVTo, conformMTo
) where

import Data.Packed.Internal.Common
import Data.Packed.Internal.Signatures
import Data.Packed.Internal.Vector

import Foreign.Marshal.Alloc(alloca, free)
import Foreign.Marshal.Array(newArray)
import Foreign.Ptr(Ptr, castPtr)
import Foreign.Storable(Storable, peekElemOff, pokeElemOff, poke, sizeOf)
import Data.Complex(Complex)
import Foreign.C.Types
import Foreign.C.String(newCString)
import System.IO.Unsafe(unsafePerformIO)
import Control.DeepSeq

-----------------------------------------------------------------

{- Design considerations for the Matrix Type
   -----------------------------------------

- we must easily handle both row major and column major order,
  for bindings to LAPACK and GSL/C

- we'd like to simplify redundant matrix transposes:
   - Some of them arise from the order requirements of some functions
   - some functions (matrix product) admit transposed arguments

- maybe we don't really need this kind of simplification:
   - more complex code
   - some computational overhead
   - only appreciable gain in code with a lot of redundant transpositions
     and cheap matrix computations

- we could carry both the matrix and its (lazily computed) transpose.
  This may save some transpositions, but it is necessary to keep track of the
  data which is actually computed to be used by functions like the matrix product
  which admit both orders.

- but if we need the transposed data and it is not in the structure, we must make
  sure that we touch the same foreignptr that is used in the computation.

- a reasonable solution is using two constructors for a matrix. Transposition just
  "flips" the constructor. Actual data transposition is not done if followed by a
  matrix product or another transpose.

-}

data MatrixOrder = RowMajor | ColumnMajor deriving (Show,Eq)

transOrder RowMajor = ColumnMajor
transOrder ColumnMajor = RowMajor
{- | Matrix representation suitable for GSL and LAPACK computations.

The elements are stored in a continuous memory array.

-}

data Matrix t = Matrix { irows :: {-# UNPACK #-} !Int
                       , icols :: {-# UNPACK #-} !Int
                       , xdat :: {-# UNPACK #-} !(Vector t)
                       , order :: !MatrixOrder }
-- RowMajor: preferred by C, fdat may require a transposition
-- ColumnMajor: preferred by LAPACK, cdat may require a transposition

cdat = xdat
fdat = xdat

rows :: Matrix t -> Int
rows = irows

cols :: Matrix t -> Int
cols = icols

orderOf :: Matrix t -> MatrixOrder
orderOf = order


-- | Matrix transpose.
trans :: Matrix t -> Matrix t
trans Matrix {irows = r, icols = c, xdat = d, order = o } = Matrix { irows = c, icols = r, xdat = d, order = transOrder o}

cmat :: (Element t) => Matrix t -> Matrix t
cmat m@Matrix{order = RowMajor} = m
cmat Matrix {irows = r, icols = c, xdat = d, order = ColumnMajor } = Matrix { irows = r, icols = c, xdat = transdata r d c, order = RowMajor}

fmat :: (Element t) => Matrix t -> Matrix t
fmat m@Matrix{order = ColumnMajor} = m
fmat Matrix {irows = r, icols = c, xdat = d, order = RowMajor } = Matrix { irows = r, icols = c, xdat = transdata c d r, order = ColumnMajor}

-- C-Haskell matrix adapter
-- mat :: Adapt (CInt -> CInt -> Ptr t -> r) (Matrix t) r

mat :: (Storable t) => Matrix t -> (((CInt -> CInt -> Ptr t -> t1) -> t1) -> IO b) -> IO b
mat a f =
    unsafeWith (xdat a) $ \p -> do
        let m g = do
            g (fi (rows a)) (fi (cols a)) p
        f m
-- | Creates a vector by concatenation of rows. If the matrix is ColumnMajor, this operation requires a transpose.
--
-- @\> flatten ('ident' 3)
-- 9 |> [1.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,1.0]@
flatten :: Element t => Matrix t -> Vector t
flatten = xdat . cmat

type Mt t s = Int -> Int -> Ptr t -> s
-- not yet admitted by my haddock version
-- infixr 6 ::>
-- type t ::> s = Mt t s

-- | the inverse of 'Data.Packed.Matrix.fromLists'
toLists :: (Element t) => Matrix t -> [[t]]
toLists m = splitEvery (cols m) . toList . flatten $ m

-- | Create a matrix from a list of vectors.
-- All vectors must have the same dimension,
-- or dimension 1, which is are automatically expanded.
fromRows :: Element t => [Vector t] -> Matrix t
fromRows vs = case compatdim (map dim vs) of
    Nothing -> error "fromRows applied to [] or to vectors with different sizes"
    Just c  -> reshape c . join . map (adapt c) $ vs
  where
    adapt c v | dim v == c = v
              | otherwise = constantD (v@>0) c

-- | extracts the rows of a matrix as a list of vectors
toRows :: Element t => Matrix t -> [Vector t]
toRows m = toRows' 0 where
    v = flatten m
    r = rows m
    c = cols m
    toRows' k | k == r*c  = []
              | otherwise = subVector k c v : toRows' (k+c)

-- | Creates a matrix from a list of vectors, as columns
fromColumns :: Element t => [Vector t] -> Matrix t
fromColumns m = trans . fromRows $ m

-- | Creates a list of vectors from the columns of a matrix
toColumns :: Element t => Matrix t -> [Vector t]
toColumns m = toRows . trans $ m

-- | Reads a matrix position.
(@@>) :: Storable t => Matrix t -> (Int,Int) -> t
infixl 9 @@>
m@Matrix {irows = r, icols = c} @@> (i,j)
    | safe      = if i<0 || i>=r || j<0 || j>=c
                    then error "matrix indexing out of range"
                    else atM' m i j
    | otherwise = atM' m i j
{-# INLINE (@@>) #-}

--  Unsafe matrix access without range checking
atM' Matrix {icols = c, xdat = v, order = RowMajor} i j = v `at'` (i*c+j)
atM' Matrix {irows = r, xdat = v, order = ColumnMajor} i j = v `at'` (j*r+i)
{-# INLINE atM' #-}

------------------------------------------------------------------

matrixFromVector o c v = Matrix { irows = r, icols = c, xdat = v, order = o }
    where (d,m) = dim v `quotRem` c
          r | m==0 = d
            | otherwise = error "matrixFromVector"

-- allocates memory for a new matrix
createMatrix :: (Storable a) => MatrixOrder -> Int -> Int -> IO (Matrix a)
createMatrix ord r c = do
    p <- createVector (r*c)
    return (matrixFromVector ord c p)

{- | Creates a matrix from a vector by grouping the elements in rows with the desired number of columns. (GNU-Octave groups by columns. To do it you can define @reshapeF r = trans . reshape r@
where r is the desired number of rows.)

@\> reshape 4 ('fromList' [1..12])
(3><4)
 [ 1.0,  2.0,  3.0,  4.0
 , 5.0,  6.0,  7.0,  8.0
 , 9.0, 10.0, 11.0, 12.0 ]@

-}
reshape :: Storable t => Int -> Vector t -> Matrix t
reshape c v = matrixFromVector RowMajor c v

singleton x = reshape 1 (fromList [x])

-- | application of a vector function on the flattened matrix elements
liftMatrix :: (Storable a, Storable b) => (Vector a -> Vector b) -> Matrix a -> Matrix b
liftMatrix f Matrix { icols = c, xdat = d, order = o } = matrixFromVector o c (f d)

-- | application of a vector function on the flattened matrices elements
liftMatrix2 :: (Element t, Element a, Element b) => (Vector a -> Vector b -> Vector t) -> Matrix a -> Matrix b -> Matrix t
liftMatrix2 f m1 m2
    | not (compat m1 m2) = error "nonconformant matrices in liftMatrix2"
    | otherwise = case orderOf m1 of
        RowMajor    -> matrixFromVector RowMajor    (cols m1) (f (xdat m1) (flatten m2))
        ColumnMajor -> matrixFromVector ColumnMajor (cols m1) (f (xdat m1) ((xdat.fmat) m2))


compat :: Matrix a -> Matrix b -> Bool
compat m1 m2 = rows m1 == rows m2 && cols m1 == cols m2

------------------------------------------------------------------

{- | Supported matrix elements.

    This class provides optimized internal
    operations for selected element types.
    It provides unoptimised defaults for any 'Storable' type,
    so you can create instances simply as:
    @instance Element Foo@.
-}
class (Storable a) => Element a where
    subMatrixD :: (Int,Int) -- ^ (r0,c0) starting position 
               -> (Int,Int) -- ^ (rt,ct) dimensions of submatrix
               -> Matrix a -> Matrix a
    subMatrixD = subMatrix'
    transdata :: Int -> Vector a -> Int -> Vector a
    transdata = transdataP -- transdata'
    constantD  :: a -> Int -> Vector a
    constantD = constantP -- constant'


instance Element Float where
    transdata  = transdataAux ctransF
    constantD  = constantAux cconstantF

instance Element Double where
    transdata  = transdataAux ctransR
    constantD  = constantAux cconstantR

instance Element (Complex Float) where
    transdata  = transdataAux ctransQ
    constantD  = constantAux cconstantQ

instance Element (Complex Double) where
    transdata  = transdataAux ctransC
    constantD  = constantAux cconstantC

-------------------------------------------------------------------

transdata' :: Storable a => Int -> Vector a -> Int -> Vector a
transdata' c1 v c2 =
    if noneed
        then v
        else unsafePerformIO $ do
                w <- createVector (r2*c2)
                unsafeWith v $ \p ->
                    unsafeWith w $ \q -> do
                        let go (-1) _ = return ()
                            go !i (-1) = go (i-1) (c1-1)
                            go !i !j = do x <- peekElemOff p (i*c1+j)
                                          pokeElemOff      q (j*c2+i) x
                                          go i (j-1)
                        go (r1-1) (c1-1)
                return w
  where r1 = dim v `div` c1
        r2 = dim v `div` c2
        noneed = r1 == 1 || c1 == 1

-- {-# SPECIALIZE transdata' :: Int -> Vector Double -> Int ->  Vector Double #-}
-- {-# SPECIALIZE transdata' :: Int -> Vector (Complex Double) -> Int -> Vector (Complex Double) #-}

-- I don't know how to specialize...
-- The above pragmas only seem to work on top level defs
-- Fortunately everything seems to work using the above class

-- C versions, still a little faster:

transdataAux fun c1 d c2 =
    if noneed
        then d
        else unsafePerformIO $ do
            v <- createVector (dim d)
            unsafeWith d $ \pd ->
                unsafeWith v $ \pv ->
                    fun (fi r1) (fi c1) pd (fi r2) (fi c2) pv // check "transdataAux"
            return v
  where r1 = dim d `div` c1
        r2 = dim d `div` c2
        noneed = r1 == 1 || c1 == 1

transdataP :: Storable a => Int -> Vector a -> Int -> Vector a
transdataP c1 d c2 =
    if noneed
       then d
       else unsafePerformIO $ do
          v <- createVector (dim d)
          unsafeWith d $ \pd ->
              unsafeWith v $ \pv ->
                  ctransP (fi r1) (fi c1) (castPtr pd) (fi sz) (fi r2) (fi c2) (castPtr pv) (fi sz) // check "transdataP"
          return v
   where r1 = dim d `div` c1
         r2 = dim d `div` c2
         sz = sizeOf (d @> 0)
         noneed = r1 == 1 || c1 == 1

foreign import ccall unsafe "transF" ctransF :: TFMFM
foreign import ccall unsafe "transR" ctransR :: TMM
foreign import ccall unsafe "transQ" ctransQ :: TQMQM
foreign import ccall unsafe "transC" ctransC :: TCMCM
foreign import ccall unsafe "transP" ctransP :: CInt -> CInt -> Ptr () -> CInt -> CInt -> CInt -> Ptr () -> CInt -> IO CInt

----------------------------------------------------------------------

constant' v n = unsafePerformIO $ do
    w <- createVector n
    unsafeWith w $ \p -> do
        let go (-1) = return ()
            go !k = pokeElemOff p k v >> go (k-1)
        go (n-1)
    return w

-- C versions

constantAux fun x n = unsafePerformIO $ do
    v <- createVector n
    px <- newArray [x]
    app1 (fun px) vec v "constantAux"
    free px
    return v

constantF :: Float -> Int -> Vector Float
constantF = constantAux cconstantF
foreign import ccall unsafe "constantF" cconstantF :: Ptr Float -> TF

constantR :: Double -> Int -> Vector Double
constantR = constantAux cconstantR
foreign import ccall unsafe "constantR" cconstantR :: Ptr Double -> TV

constantQ :: Complex Float -> Int -> Vector (Complex Float)
constantQ = constantAux cconstantQ
foreign import ccall unsafe "constantQ" cconstantQ :: Ptr (Complex Float) -> TQV

constantC :: Complex Double -> Int -> Vector (Complex Double)
constantC = constantAux cconstantC
foreign import ccall unsafe "constantC" cconstantC :: Ptr (Complex Double) -> TCV

constantP :: Storable a => a -> Int -> Vector a
constantP a n = unsafePerformIO $ do
    let sz = sizeOf a
    v <- createVector n
    unsafeWith v $ \p -> do
       alloca $ \k -> do
                      poke k a
                      cconstantP (castPtr k) (fi n) (castPtr p) (fi sz) // check "constantP"
    return v
foreign import ccall unsafe "constantP" cconstantP :: Ptr () -> CInt -> Ptr () -> CInt -> IO CInt

----------------------------------------------------------------------

-- | Extracts a submatrix from a matrix.
subMatrix :: Element a
          => (Int,Int) -- ^ (r0,c0) starting position 
          -> (Int,Int) -- ^ (rt,ct) dimensions of submatrix
          -> Matrix a -- ^ input matrix
          -> Matrix a -- ^ result
subMatrix (r0,c0) (rt,ct) m
    | 0 <= r0 && 0 < rt && r0+rt <= (rows m) &&
      0 <= c0 && 0 < ct && c0+ct <= (cols m) = subMatrixD (r0,c0) (rt,ct) m
    | otherwise = error $ "wrong subMatrix "++
                          show ((r0,c0),(rt,ct))++" of "++show(rows m)++"x"++ show (cols m)

subMatrix'' (r0,c0) (rt,ct) c v = unsafePerformIO $ do
    w <- createVector (rt*ct)
    unsafeWith v $ \p ->
        unsafeWith w $ \q -> do
            let go (-1) _ = return ()
                go !i (-1) = go (i-1) (ct-1)
                go !i !j = do x <- peekElemOff p ((i+r0)*c+j+c0)
                              pokeElemOff      q (i*ct+j) x
                              go i (j-1)
            go (rt-1) (ct-1)
    return w

subMatrix' (r0,c0) (rt,ct) (Matrix { icols = c, xdat = v, order = RowMajor}) = Matrix rt ct (subMatrix'' (r0,c0) (rt,ct) c v) RowMajor
subMatrix' (r0,c0) (rt,ct) m = trans $ subMatrix' (c0,r0) (ct,rt) (trans m)

--------------------------------------------------------------------------

-- | Saves a matrix as 2D ASCII table.
saveMatrix :: FilePath
           -> String     -- ^ format (%f, %g, %e)
           -> Matrix Double
           -> IO ()
saveMatrix filename fmt m = do
    charname <- newCString filename
    charfmt <- newCString fmt
    let o = if orderOf m == RowMajor then 1 else 0
    app1 (matrix_fprintf charname charfmt o) mat m "matrix_fprintf"
    free charname
    free charfmt

foreign import ccall unsafe "matrix_fprintf" matrix_fprintf :: Ptr CChar -> Ptr CChar -> CInt -> TM

----------------------------------------------------------------------

conformMs ms = map (conformMTo (r,c)) ms
  where
    r = maximum (map rows ms)
    c = maximum (map cols ms)

conformVs vs = map (conformVTo n) vs
  where
    n = maximum (map dim vs)

conformMTo (r,c) m
    | size m == (r,c) = m
    | size m == (1,1) = reshape c (constantD (m@@>(0,0)) (r*c))
    | size m == (r,1) = repCols c m
    | size m == (1,c) = repRows r m
    | otherwise = error $ "matrix " ++ shSize m ++ " cannot be expanded to (" ++ show r ++ "><"++ show c ++")"

conformVTo n v
    | dim v == n = v
    | dim v == 1 = constantD (v@>0) n
    | otherwise = error $ "vector of dim=" ++ show (dim v) ++ " cannot be expanded to dim=" ++ show n

repRows n x = fromRows (replicate n (flatten x))
repCols n x = fromColumns (replicate n (flatten x))

size m = (rows m, cols m)

shSize m = "(" ++ show (rows m) ++"><"++ show (cols m)++")"

----------------------------------------------------------------------

instance (Storable t, NFData t) => NFData (Matrix t)
  where
    rnf m | d > 0     = rnf (v @> 0)
          | otherwise = ()
      where
        d = dim v
        v = xdat m

