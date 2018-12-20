{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module GetSet3 where

import Language.Haskell.Liquid.ProofCombinators

{-@ data State [stLen] @-}

data State = State 
  { sVals :: [(Int, Int)] -- ^ binders and their values
  , sDef  :: Int          -- ^ default value (for missing binder)
  }  

{-@ measure stLen @-} 
{-@ stLen :: State -> Nat @-}
stLen :: State -> Int 
stLen (State xs _) = llen xs  

{-@ measure llen @-}
{-@ llen :: [a] -> Nat @-}
llen :: [a] -> Int
llen [] = 0 
llen (x:xs) = 1 + llen xs 

{-@ reflect set @-}
set :: State -> Int -> Int  -> State 
set (State kvs v0) k v = State ((k,v) : kvs) v0 

{-@ reflect getDefault @-}
getDefault :: Int -> Int -> [(Int, Int)] -> Int 
getDefault v0 key ((k, v) : kvs) 
  | key == k       = v 
  | otherwise      = getDefault v0 key kvs 
getDefault v0 _ [] = v0 

{-@ reflect get @-}
get :: State -> Int -> Int 

-- BAD
-- get (State kvs v0) key = getDefault v0 key kvs

-- OK, WTF
get (State [] v0) key = v0 
get (State ((k,v):kvs) v0) key = if key == k then v else get (State kvs v0) key 

--- 

{-@ ugh :: s:State -> { s1:State | get s1 66 == 10 } @-}
ugh :: State -> State  
ugh s = set s 66 10

{-@ ok :: s:State -> { get (set s 66 10) 66 == 10 } @-}
ok :: State -> () 
ok s = ()


{-@ lemma_get_not_set :: k0:_ -> k:{k /= k0} -> val:_ -> s:_ -> { get (set s k val) k0 = get s k0 }  @-}
lemma_get_not_set :: Int -> Int -> Int -> State -> Proof 
lemma_get_not_set _ _ _ _ = ()

