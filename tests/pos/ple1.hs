{-@ LIQUID "--exact-data-cons" @-}
{- LIQUID "--no-adt"          @-}

module PLE where

import Prelude hiding ((++))
import Language.Haskell.Liquid.ProofCombinators

assocThm :: (Eq a) => [a] -> [a] -> [a] -> Bool
assocProof :: [a] -> [a] -> [a] -> Proof

{-@ infix ++ @-}

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

{-@ inline assocThm @-}
assocThm xs ys zs = (xs ++ ys) ++ zs == xs ++ (ys ++ zs)

{-@ assocProof :: xs:[a] -> ys:[a] -> zs:[a] -> { assocThm xs ys zs } @-}
assocProof []     ys zs
  =   ([] ++ ys) ++ zs
  ==. [] ++ (ys ++ zs)
  *** QED

assocProof (x:xs) ys zs
  =   ((x:xs) ++ ys) ++ zs
  ==. (x : (xs ++ ys)) ++ zs
  ==. x : ((xs ++ ys) ++ zs)
  ==. x : (xs ++ (ys ++ zs)) ? assocProof xs ys zs
  ==. (x:xs) ++ (ys ++ zs)
  ***  QED

















---
