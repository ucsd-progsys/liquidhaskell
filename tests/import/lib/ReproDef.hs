{-@ LIQUID "--reflection" @-}

{-# LANGUAGE GADTs #-}

module ReproDef where

data Evidence where
  {-@ Refuter :: p:Int
              -> (x:{Int | x == p} -> {v:() | 0 /= 0})
              -> Evidence @-}
  Refuter :: Int -> (Int -> ()) -> Evidence

{-@ contradictionHere :: Evidence -> {v:() | 0 /= 0} @-}
contradictionHere :: Evidence -> ()
contradictionHere (Refuter p contra) = contra p
