{-# LANGUAGE FlexibleContexts #-}
-----------------------------------------------------------------------------
{- |
Module      :  Numeric.LinearAlgebra.Util.Convolution
Copyright   :  (c) Alberto Ruiz 2012
License     :  GPL

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional

-}
-----------------------------------------------------------------------------

module Numeric.LinearAlgebra.Util.Convolution(
   corr, conv, corrMin,
   corr2, conv2, separable
) where

import Numeric.LinearAlgebra


vectSS :: Element t => Int -> Vector t -> Matrix t
vectSS n v = fromRows [ subVector k n v | k <- [0 .. dim v - n] ]


corr :: Product t => Vector t -- ^ kernel
                  -> Vector t -- ^ source
                  -> Vector t
{- ^ correlation

>>> corr (fromList[1,2,3]) (fromList [1..10])
fromList [14.0,20.0,26.0,32.0,38.0,44.0,50.0,56.0]

-}
corr ker v | dim ker <= dim v = vectSS (dim ker) v <> ker
           | otherwise = error $ "corr: dim kernel ("++show (dim ker)++") > dim vector ("++show (dim v)++")"


conv :: (Product t, Num t) => Vector t -> Vector t -> Vector t
{- ^ convolution ('corr' with reversed kernel and padded input, equivalent to polynomial product)

>>> conv (fromList[1,1]) (fromList [-1,1])
fromList [-1.0,0.0,1.0]

-}
conv ker v = corr ker' v'
  where
    ker' = (flatten.fliprl.asRow) ker
    v' | dim ker > 1 = join [z,v,z]
       | otherwise   = v
    z = constant 0 (dim ker -1)

corrMin :: (Container Vector t, RealElement t, Product t)
        => Vector t
        -> Vector t
        -> Vector t
-- ^ similar to 'corr', using 'min' instead of (*)
corrMin ker v = minEvery ss (asRow ker) <> ones
  where
    minEvery a b = cond a b a a b
    ss = vectSS (dim ker) v
    ones = konst' 1 (dim ker)



matSS :: Element t => Int -> Matrix t -> [Matrix t]
matSS dr m = map (reshape c) [ subVector (k*c) n v | k <- [0 .. r - dr] ]
  where
    v = flatten m
    c = cols m
    r = rows m
    n = dr*c


corr2 :: Product a => Matrix a -> Matrix a -> Matrix a
-- ^ 2D correlation
corr2 ker mat = dims
              . concatMap (map ((<.> ker') . flatten) . matSS c . trans)
              . matSS r $ mat
  where
    r = rows ker
    c = cols ker
    ker' = flatten (trans ker)
    rr = rows mat - r + 1
    rc = cols mat - c + 1
    dims | rr > 0 && rc > 0 = (rr >< rc)
         | otherwise = error $ "corr2: dim kernel ("++sz ker++") > dim matrix ("++sz mat++")"
    sz m = show (rows m)++"x"++show (cols m)

conv2 :: (Num a, Product a) => Matrix a -> Matrix a -> Matrix a
-- ^ 2D convolution
conv2 k m = corr2 (fliprl . flipud $ k) pm
  where
    pm | r == 0 && c == 0 = m
       | r == 0           = fromBlocks [[z3,m,z3]]
       |           c == 0 = fromBlocks [[z2],[m],[z2]]
       | otherwise        = fromBlocks [[z1,z2,z1]
                                       ,[z3, m,z3]
                                       ,[z1,z2,z1]]
    r = rows k - 1
    c = cols k - 1
    h = rows m
    w = cols m
    z1 = konst' 0 (r,c)
    z2 = konst' 0 (r,w)
    z3 = konst' 0 (h,c)

-- TODO: could be simplified using future empty arrays


separable :: Element t => (Vector t -> Vector t) -> Matrix t -> Matrix t
-- ^ matrix computation implemented as separated vector operations by rows and columns.
separable f = fromColumns . map f . toColumns . fromRows . map f . toRows

