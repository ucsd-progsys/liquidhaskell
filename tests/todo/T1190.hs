{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--ple"            @-}

module Intervals where

import qualified Data.Set as S
import Language.Haskell.Liquid.NewProofCombinators

{-@ reflect sem_ij @-}
{-@ sem_ij :: i:Int -> j:Int -> S.Set Int / [j - i] @-}
sem_ij :: Int -> Int -> S.Set Int
sem_ij i j
  | i < j     = S.union (S.singleton i) (sem_ij (i+1) j)
  | otherwise = S.empty

{-@ lem_mem :: f:Int -> t:Int -> x:{Int| x < f || t <= x} -> { not (S.member x (sem_ij f t)) } / [t - f]
  @-}
lem_mem :: Int -> Int -> Int -> ()
lem_mem f t x
  | f < t     =  lem_mem (f + 1) t x
  | otherwise =  ()

{-@ lem_disj :: f1:_ -> t1:_ -> f2:{Int | t1 <= f2 } -> t2:Int  ->
                   { S.intersection (sem_ij f1 t1) (sem_ij f2 t2) = S.empty } / [t2 - f2]
  @-}
lem_disj :: Int -> Int -> Int -> Int -> ()
lem_disj f1 t1 f2 t2
  | f2 < t2   =  lem_mem f1 t1 f2 &&& lem_disj f1 t1 (f2 + 1) t2
  | otherwise = ()
