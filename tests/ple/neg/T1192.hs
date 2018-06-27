{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--ple"            @-}

module RangeSet where

import qualified Data.Set as S

import Language.Haskell.Liquid.NewProofCombinators

{-@ reflect sem_ij @-}
{-@ sem_ij :: i:Int -> j:Int -> S.Set Int / [j - i] @-}
sem_ij :: Int -> Int -> S.Set Int
sem_ij i j
  | i < j     = S.union (S.singleton i) (sem_ij (i+1) j)
  | otherwise = S.empty

{-@ lem_split :: f:_ -> x:{_ | f <= x} -> t:{_ | x < t} ->
                { sem_ij f t = S.union (sem_ij f x) (sem_ij x t) } / [ x - f]
  @-}
lem_split :: Int -> Int -> Int -> ()
lem_split f x t
  | f == x = ()
  | f <  x = ()
