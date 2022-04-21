-- some tests of the interface for pure
-- computations with inplace updates

import Numeric.LinearAlgebra
import Data.Packed.ST
import Data.Packed.Convert

import Data.Array.Unboxed
import Data.Array.ST
import Control.Monad.ST
import Control.Monad

main = sequence_[
    print test1,
    print test2,
    print test3,
    print test4,
    test5,
    test6,
    print test7,
    test8,
    test0]

-- helper functions
vector l = fromList l :: Vector Double
norm v = pnorm PNorm2 v

-- hmatrix vector and matrix
v = vector [1..10]
m = (5><10) [1..50::Double]

----------------------------------------------------------------------

-- vector creation by in-place updates on a copy of the argument
test1 = fun v

fun :: Element t => Vector t -> Vector t
fun x = runSTVector $ do
    a <- thawVector x
    mapM_ (flip (modifyVector a) (+57)) [0 .. dim x `div` 2 - 1]
    return a

-- another example: creation of an antidiagonal matrix from a list
test2 = antiDiag 5 8 [1..] :: Matrix Double

antiDiag :: (Element b) => Int -> Int -> [b] -> Matrix b
antiDiag r c l = runSTMatrix $ do
    m <- newMatrix 0 r c
    let d = min r c - 1
    sequence_ $ zipWith (\i v -> writeMatrix m i (c-1-i) v) [0..d] l
    return m

-- using vector or matrix functions on mutable objects requires freezing:
test3 = g1 v

g1 x = runST $ do
    a <- thawVector x
    writeVector a (dim x -1) 0
    b <- freezeVector a
    return (norm b)

--  another possibility:
test4 = g2 v

g2 x = runST $ do
    a <- thawVector x
    writeVector a (dim x -1) 0
    t <- liftSTVector norm a
    return t

--------------------------------------------------------------

-- haskell arrays
hv = listArray (0,9) [1..10::Double]
hm = listArray ((0,0),(4,9)) [1..50::Double]



-- conversion from standard Haskell arrays
test5 = do
    print $ norm (vectorFromArray hv)
    print $ norm v
    print $ rcond (matrixFromArray hm)
    print $ rcond m


-- conversion to mutable ST arrays
test6 = do
    let y = clearColumn m 1
    print y
    print (matrixFromArray y)

clearColumn x c = runSTUArray $ do
    a <- mArrayFromMatrix x
    forM_ [0..rows x-1] $ \i->
        writeArray a (i,c) (0::Double)
    return a

-- hmatrix functions applied to mutable ST arrays
test7 = unitary (listArray (1,4) [3,5,7,2] :: UArray Int Double)

unitary v = runSTUArray $ do
    a <- thaw v
    n <- norm `fmap` vectorFromMArray a
    b <- mapArray (/n) a
    return b

-------------------------------------------------

-- (just to check that they are not affected)
test0 = do
    print v
    print m
    --print hv
    --print hm

-------------------------------------------------

histogram n ds = runSTVector $ do
    h <- newVector (0::Double) n -- number of bins
    let inc k = modifyVector h k (+1)
    mapM_ inc ds
    return h

-- check that newVector is really called with a fresh new array
histoCheck ds = runSTVector $ do
    h <- newVector (0::Double) 15 -- > constant for this test
    let inc k = modifyVector h k (+1)
    mapM_ inc ds
    return h

hc = fromList [1 .. 15::Double]

-- check that thawVector creates a new array
histoCheck2 ds = runSTVector $ do
    h <- thawVector hc
    let inc k = modifyVector h k (+1)
    mapM_ inc ds
    return h

test8 = do
    let ds = [0..14]
    print $ histogram 15 ds
    print $ histogram 15 ds
    print $ histogram 15 ds
    print $ histoCheck ds
    print $ histoCheck ds
    print $ histoCheck ds
    print $ histoCheck2 ds
    print $ histoCheck2 ds
    print $ histoCheck2 ds
    putStrLn "----------------------"
