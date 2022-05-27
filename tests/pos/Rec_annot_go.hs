{-# LANGUAGE ScopedTypeVariables #-}

module Rec_annot_go () where

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ invariant {v:Int | v >= 0} @-}

{-@ decrease go 1 @-}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a 
loop lo hi base f = go (hi-lo) base lo
  where
    go (d::Int) acc i     
      | i /= hi   = go (d-1) (f i acc) (i + 1)
      | otherwise = acc

poo = loop 0 10 0 (+)

