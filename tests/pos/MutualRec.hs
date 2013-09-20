{-# LANGUAGE ScopedTypeVariables #-}

module MutualRec where

import Language.Haskell.Liquid.Prelude


bin :: k -> v -> [(k, v)] -> [(k, v)] -> [(k, v)] 
{-@ bin :: k -> v -> [(k, v)] -> [(k, v)] -> [(k, v)] @-}
singleton :: k -> v -> [(k, v)]
{-@ singleton :: k -> v -> [(k, v)] @-}
bin = undefined
singleton = undefined

fromDistinctAscList xs
  = create const (length xs) xs
  where
    {-@ Decrease create  2 3 @-}
    {-@ Decrease createR 1 4 @-}
    create c (0::Int) xs' = c undefined xs'
-- LIQUID for n = 1 n `div` 2 = 0 and the assume does not hold
    create c 1 xs' = case xs' of
                       (k1,x1):xx -> c (singleton k1 x1) xx
                       _ -> error "fromDistinctAscList create"
    create c 5 xs' = case xs' of
                       ((k1,x1):(k2,x2):(k3,x3):(k4,x4):(k5,x5):xx)
                            -> c (bin k4 x4 (bin k2 x2 (singleton k1 x1) (singleton k3 x3)) (singleton k5 x5)) xx
                       _ -> error "fromDistinctAscList create"
    create c n xs' = seq nr $ create (createR nr c) nl xs'
      where nl = liquidAssume (m < n && m >= 0) m
            m  = n `div` 2
            nr = n - nl - 1

    createR (n::Int) c l ((k,x):ys) = create (createB l k x c) n ys
    createR _ _ _ []         = error "fromDistinctAscList createR []"
    createB l k x c r zs     = c (bin k x l r) zs


