
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

module T1112 where

import T1112Lib

{- data Product @-}

{-@ axiomatize leqProd @-}
leqProd :: Eq (f p)
        => (f p -> f p -> Bool) -> (g p -> g p -> Bool)
        -> Product f g p -> Product f g p -> Bool
leqProd leqFP leqGP (Product x1 y1) (Product x2 y2) =
  if x1 == x2
    then leqGP y1 y2
    else leqFP x1 x2
{-# INLINE leqProd #-}
