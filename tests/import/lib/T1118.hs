{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
module T1118 where

import T1118Lib2 
import T1118Lib1
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize leqU1 @-}
leqU1 :: U1 p -> U1 p -> Bool
leqU1 _ _ = True

{-@ leqU1Refl :: x:U1 p -> { leqU1 x x } @-}
leqU1Refl :: U1 p -> Proof
leqU1Refl U1 = leqU1 U1 U1 ==. True *** QED

{-@ axiomatize leqProd @-}
leqProd :: Eq (f p)
        => (f p -> f p -> Bool) -> (g p -> g p -> Bool)
        -> Product f g p -> Product f g p -> Bool
leqProd leqFP leqGP (Product x1 y1) (Product x2 y2) =
  if x1 == x2
    then leqGP y1 y2
    else leqFP x1 x2
{-# INLINE leqProd #-}
