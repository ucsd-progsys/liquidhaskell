{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.Matrix
-- Copyright   :  (c) Alberto Ruiz 2007-10
-- License     :  GPL
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
--
-- A Matrix representation suitable for numerical computations using LAPACK and GSL.
--
-- This module provides basic functions for manipulation of structure.

-----------------------------------------------------------------------------

module Data.Packed.Matrix (
    Matrix,
    Element,
    rows,cols,
    (><),
    trans,
    reshape, flatten,
    fromLists, toLists, buildMatrix,
    (@@>),
    asRow, asColumn,
    fromRows, toRows, fromColumns, toColumns,
    fromBlocks, diagBlock, toBlocks, toBlocksEvery,
    repmat,
    flipud, fliprl,
    subMatrix, takeRows, dropRows, takeColumns, dropColumns,
    extractRows,
    diagRect, takeDiag,
    mapMatrix, mapMatrixWithIndex, mapMatrixWithIndexM, mapMatrixWithIndexM_,
    liftMatrix, liftMatrix2, liftMatrix2Auto,fromArray2D
) where

import Data.Packed.Internal
import qualified Data.Packed.ST as ST
import Data.Array

import Data.List(transpose,intersperse)
import Foreign.Storable(Storable)
import Control.Monad(liftM)

-------------------------------------------------------------------

#ifdef BINARY

import Data.Binary
import Control.Monad(replicateM)

instance (Binary a, Element a, Storable a) => Binary (Matrix a) where
    put m = do
            let r = rows m
            let c = cols m
            put r
            put c
            mapM_ (\i -> mapM_ (\j -> put $ m @@> (i,j)) [0..(c-1)]) [0..(r-1)]
    get = do
          r <- get
          c <- get
          xs <- replicateM r $ replicateM c get
          return $ fromLists xs

#endif

-------------------------------------------------------------------

instance (Show a, Element a) => (Show (Matrix a)) where
    show m = (sizes++) . dsp . map (map show) . toLists $ m
        where sizes = "("++show (rows m)++"><"++show (cols m)++")\n"

dsp as = (++" ]") . (" ["++) . init . drop 2 . unlines . map (" , "++) . map unwords' $ transpose mtp
    where
        mt = transpose as
        longs = map (maximum . map length) mt
        mtp = zipWith (\a b -> map (pad a) b) longs mt
        pad n str = replicate (n - length str) ' ' ++ str
        unwords' = concat . intersperse ", "

------------------------------------------------------------------

instance (Element a, Read a) => Read (Matrix a) where
    readsPrec _ s = [((rs><cs) . read $ listnums, rest)]
        where (thing,rest) = breakAt ']' s
              (dims,listnums) = breakAt ')' thing
              cs = read . init . fst. breakAt ')' . snd . breakAt '<' $ dims
              rs = read . snd . breakAt '(' .init . fst . breakAt '>' $ dims


breakAt c l = (a++[c],tail b) where
    (a,b) = break (==c) l

------------------------------------------------------------------

-- | creates a matrix from a vertical list of matrices
joinVert :: Element t => [Matrix t] -> Matrix t
joinVert ms = case common cols ms of
    Nothing -> error "(impossible) joinVert on matrices with different number of columns"
    Just c  -> reshape c $ join (map flatten ms)

-- | creates a matrix from a horizontal list of matrices
joinHoriz :: Element t => [Matrix t] -> Matrix t
joinHoriz ms = trans. joinVert . map trans $ ms

{- | Creates a matrix from blocks given as a list of lists of matrices.

Single row/column components are automatically expanded to match the
corresponding common row and column:

@\> let disp = putStr . dispf 2
\> let vector xs = fromList xs :: Vector Double
\> let diagl = diag . vector
\> let rowm = asRow . vector

\> disp $ fromBlocks [[ident 5, 7, rowm[10,20]], [3, diagl[1,2,3], 0]]

8x10
1  0  0  0  0  7  7  7  10  20
0  1  0  0  0  7  7  7  10  20
0  0  1  0  0  7  7  7  10  20
0  0  0  1  0  7  7  7  10  20
0  0  0  0  1  7  7  7  10  20
3  3  3  3  3  1  0  0   0   0
3  3  3  3  3  0  2  0   0   0
3  3  3  3  3  0  0  3   0   0@
-}
fromBlocks :: Element t => [[Matrix t]] -> Matrix t
fromBlocks = fromBlocksRaw . adaptBlocks

fromBlocksRaw mms = joinVert . map joinHoriz $ mms

adaptBlocks ms = ms' where
    bc = case common length ms of
          Just c -> c
          Nothing -> error "fromBlocks requires rectangular [[Matrix]]"
    rs = map (compatdim . map rows) ms
    cs = map (compatdim . map cols) (transpose ms)
    szs = sequence [rs,cs]
    ms' = splitEvery bc $ zipWith g szs (concat ms)

    g [Just nr,Just nc] m
                | nr == r && nc == c = m
                | r == 1 && c == 1 = reshape nc (constantD x (nr*nc))
                | r == 1 = fromRows (replicate nr (flatten m))
                | otherwise = fromColumns (replicate nc (flatten m))
      where
        r = rows m
        c = cols m
        x = m@@>(0,0)
    g _ _ = error "inconsistent dimensions in fromBlocks"


--------------------------------------------------------------------------------

-- | create a block diagonal matrix
diagBlock :: (Element t, Num t) => [Matrix t] -> Matrix t
diagBlock ms = fromBlocks $ zipWith f ms [0..]
  where
    f m k = take n $ replicate k z ++ m : repeat z
    n = length ms
    z = (1><1) [0]

--------------------------------------------------------------------------------


-- | Reverse rows
flipud :: Element t => Matrix t -> Matrix t
flipud m = fromRows . reverse . toRows $ m

-- | Reverse columns
fliprl :: Element t => Matrix t -> Matrix t
fliprl m = fromColumns . reverse . toColumns $ m

------------------------------------------------------------

{- | creates a rectangular diagonal matrix:

@> diagRect 7 (fromList [10,20,30]) 4 5 :: Matrix Double
(4><5)
 [ 10.0,  7.0,  7.0, 7.0, 7.0
 ,  7.0, 20.0,  7.0, 7.0, 7.0
 ,  7.0,  7.0, 30.0, 7.0, 7.0
 ,  7.0,  7.0,  7.0, 7.0, 7.0 ]@
-}
diagRect :: (Storable t) => t -> Vector t -> Int -> Int -> Matrix t
diagRect z v r c = ST.runSTMatrix $ do
        m <- ST.newMatrix z r c
        let d = min r c `min` (dim v)
        mapM_ (\k -> ST.writeMatrix m k k (v@>k)) [0..d-1]
        return m

-- | extracts the diagonal from a rectangular matrix
takeDiag :: (Element t) => Matrix t -> Vector t
takeDiag m = fromList [flatten m `at` (k*cols m+k) | k <- [0 .. min (rows m) (cols m) -1]]

------------------------------------------------------------

{- | An easy way to create a matrix:

@\> (2><3)[1..6]
(2><3)
 [ 1.0, 2.0, 3.0
 , 4.0, 5.0, 6.0 ]@

This is the format produced by the instances of Show (Matrix a), which
can also be used for input.

The input list is explicitly truncated, so that it can
safely be used with lists that are too long (like infinite lists).

Example:

@\> (2><3)[1..]
(2><3)
 [ 1.0, 2.0, 3.0
 , 4.0, 5.0, 6.0 ]@

-}
(><) :: (Storable a) => Int -> Int -> [a] -> Matrix a
r >< c = f where
    f l | dim v == r*c = matrixFromVector RowMajor c v
        | otherwise    = error $ "inconsistent list size = "
                                 ++show (dim v) ++" in ("++show r++"><"++show c++")"
        where v = fromList $ take (r*c) l

----------------------------------------------------------------

-- | Creates a matrix with the first n rows of another matrix
takeRows :: Element t => Int -> Matrix t -> Matrix t
takeRows n mt = subMatrix (0,0) (n, cols mt) mt
-- | Creates a copy of a matrix without the first n rows
dropRows :: Element t => Int -> Matrix t -> Matrix t
dropRows n mt = subMatrix (n,0) (rows mt - n, cols mt) mt
-- |Creates a matrix with the first n columns of another matrix
takeColumns :: Element t => Int -> Matrix t -> Matrix t
takeColumns n mt = subMatrix (0,0) (rows mt, n) mt
-- | Creates a copy of a matrix without the first n columns
dropColumns :: Element t => Int -> Matrix t -> Matrix t
dropColumns n mt = subMatrix (0,n) (rows mt, cols mt - n) mt

----------------------------------------------------------------

{- | Creates a 'Matrix' from a list of lists (considered as rows).

@\> fromLists [[1,2],[3,4],[5,6]]
(3><2)
 [ 1.0, 2.0
 , 3.0, 4.0
 , 5.0, 6.0 ]@
-}
fromLists :: Element t => [[t]] -> Matrix t
fromLists = fromRows . map fromList

-- | creates a 1-row matrix from a vector
asRow :: Storable a => Vector a -> Matrix a
asRow v = reshape (dim v) v

-- | creates a 1-column matrix from a vector
asColumn :: Storable a => Vector a -> Matrix a
asColumn v = reshape 1 v



{- | creates a Matrix of the specified size using the supplied function to
     to map the row\/column position to the value at that row\/column position.

@> buildMatrix 3 4 (\\(r,c) -> fromIntegral r * fromIntegral c)
(3><4)
 [ 0.0, 0.0, 0.0, 0.0, 0.0
 , 0.0, 1.0, 2.0, 3.0, 4.0
 , 0.0, 2.0, 4.0, 6.0, 8.0]@

Hilbert matrix of order N:

@hilb n = buildMatrix n n (\\(i,j)->1/(fromIntegral i + fromIntegral j +1))@

-}
buildMatrix :: Element a => Int -> Int -> ((Int, Int) -> a) -> Matrix a
buildMatrix rc cc f =
    fromLists $ map (map f)
        $ map (\ ri -> map (\ ci -> (ri, ci)) [0 .. (cc - 1)]) [0 .. (rc - 1)]

-----------------------------------------------------

fromArray2D :: (Storable e) => Array (Int, Int) e -> Matrix e
fromArray2D m = (r><c) (elems m)
    where ((r0,c0),(r1,c1)) = bounds m
          r = r1-r0+1
          c = c1-c0+1


-- | rearranges the rows of a matrix according to the order given in a list of integers.
extractRows :: Element t => [Int] -> Matrix t -> Matrix t
extractRows l m = fromRows $ extract (toRows m) l
    where extract l' is = [l'!!i |i<-is]

{- | creates matrix by repetition of a matrix a given number of rows and columns

@> repmat (ident 2) 2 3 :: Matrix Double
(4><6)
 [ 1.0, 0.0, 1.0, 0.0, 1.0, 0.0
 , 0.0, 1.0, 0.0, 1.0, 0.0, 1.0
 , 1.0, 0.0, 1.0, 0.0, 1.0, 0.0
 , 0.0, 1.0, 0.0, 1.0, 0.0, 1.0 ]@

-}
repmat :: (Element t) => Matrix t -> Int -> Int -> Matrix t
repmat m r c = fromBlocks $ splitEvery c $ replicate (r*c) m

-- | A version of 'liftMatrix2' which automatically adapt matrices with a single row or column to match the dimensions of the other matrix.
liftMatrix2Auto :: (Element t, Element a, Element b) => (Vector a -> Vector b -> Vector t) -> Matrix a -> Matrix b -> Matrix t
liftMatrix2Auto f m1 m2
    | compat' m1 m2 = lM f m1  m2
    | ok            = lM f m1' m2'
    | otherwise = error $ "nonconformable matrices in liftMatrix2Auto: " ++ shSize m1 ++ ", " ++ shSize m2
  where
    (r1,c1) = size m1
    (r2,c2) = size m2
    r = max r1 r2
    c = max c1 c2
    r0 = min r1 r2
    c0 = min c1 c2
    ok = r0 == 1 || r1 == r2 && c0 == 1 || c1 == c2
    m1' = conformMTo (r,c) m1
    m2' = conformMTo (r,c) m2

lM f m1 m2 = reshape (max (cols m1) (cols m2)) (f (flatten m1) (flatten m2))

compat' :: Matrix a -> Matrix b -> Bool
compat' m1 m2 = s1 == (1,1) || s2 == (1,1) || s1 == s2
  where
    s1 = size m1
    s2 = size m2

------------------------------------------------------------

toBlockRows [r] m | r == rows m = [m]
toBlockRows rs m = map (reshape (cols m)) (takesV szs (flatten m))
    where szs = map (* cols m) rs

toBlockCols [c] m | c == cols m = [m]
toBlockCols cs m = map trans . toBlockRows cs . trans $ m

-- | Partition a matrix into blocks with the given numbers of rows and columns.
-- The remaining rows and columns are discarded.
toBlocks :: (Element t) => [Int] -> [Int] -> Matrix t -> [[Matrix t]]
toBlocks rs cs m = map (toBlockCols cs) . toBlockRows rs $ m

-- | Fully partition a matrix into blocks of the same size. If the dimensions are not
-- a multiple of the given size the last blocks will be smaller.
toBlocksEvery :: (Element t) => Int -> Int -> Matrix t -> [[Matrix t]]
toBlocksEvery r c m = toBlocks rs cs m where
    (qr,rr) = rows m `divMod` r
    (qc,rc) = cols m `divMod` c
    rs = replicate qr r ++ if rr > 0 then [rr] else []
    cs = replicate qc c ++ if rc > 0 then [rc] else []

-------------------------------------------------------------------

-- Given a column number and a function taking matrix indexes, returns
-- a function which takes vector indexes (that can be used on the
-- flattened matrix).
mk :: Int -> ((Int, Int) -> t) -> (Int -> t)
mk c g = \k -> g (divMod k c)

{- |

@ghci> mapMatrixWithIndexM_ (\\(i,j) v -> printf \"m[%.0f,%.0f] = %.f\\n\" i j v :: IO()) ((2><3)[1 :: Double ..])
m[0,0] = 1
m[0,1] = 2
m[0,2] = 3
m[1,0] = 4
m[1,1] = 5
m[1,2] = 6@
-}
mapMatrixWithIndexM_
  :: (Element a, Num a, Monad m) =>
      ((Int, Int) -> a -> m ()) -> Matrix a -> m ()
mapMatrixWithIndexM_ g m = mapVectorWithIndexM_ (mk c g) . flatten $ m
  where
    c = cols m

{- |

@ghci> mapMatrixWithIndexM (\\(i,j) v -> Just $ 100*v + 10*i + j) (ident 3:: Matrix Double)
Just (3><3)
 [ 100.0,   1.0,   2.0
 ,  10.0, 111.0,  12.0
 ,  20.0,  21.0, 122.0 ]@
-}
mapMatrixWithIndexM
  :: (Element a, Storable b, Monad m) =>
      ((Int, Int) -> a -> m b) -> Matrix a -> m (Matrix b)
mapMatrixWithIndexM g m = liftM (reshape c) . mapVectorWithIndexM (mk c g) . flatten $ m 
    where
      c = cols m

{- |
@ghci> mapMatrixWithIndex (\\(i,j) v -> 100*v + 10*i + j) (ident 3:: Matrix Double)
(3><3)
 [ 100.0,   1.0,   2.0
 ,  10.0, 111.0,  12.0
 ,  20.0,  21.0, 122.0 ]@
 -}
mapMatrixWithIndex
  :: (Element a, Storable b) =>
      ((Int, Int) -> a -> b) -> Matrix a -> Matrix b
mapMatrixWithIndex g m = reshape c . mapVectorWithIndex (mk c g) . flatten $ m
    where
      c = cols m

mapMatrix :: (Storable a, Storable b) => (a -> b) -> Matrix a -> Matrix b
mapMatrix f = liftMatrix (mapVector f)
