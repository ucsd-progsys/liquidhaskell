{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module GetSet3 where

import Language.Haskell.Liquid.ProofCombinators

type Vname = String
type Val   = Int 
type State = GState Vname Val 

data GState k v = GState 
  { sVals :: [(k, v)] -- ^ binders and their values
  , sDef  :: v        -- ^ default value (for missing binder)
  }  

{-@ reflect set @-}
set :: GState k v -> k -> v -> GState k v 
set (GState kvs v0) k v = GState ((k,v) : kvs) v0 

{-@ reflect getDefault @-}
getDefault :: (Eq k) => v -> k -> [(k, v)] -> v
getDefault v0 key ((k, v) : kvs) 
  | key == k          = v 
  | otherwise         = getDefault v0 key kvs 
getDefault v0 _ [] = v0 

{-@ reflect get @-}
get :: (Eq k) => GState k v -> k -> v 
-- BAD get (GState kvs v0) key = getDefault v0 key kvs
-- TODO: OK???!!!
get (GState [] v0) key = v0
get (GState ((k,v):kvs) v0) key = if key == k then v else get (GState kvs v0) key


type IState = GState Int Int 

{-@ goo :: s:IState -> { s1:IState | get s1 66 == 10 } @-}
goo :: IState -> IState  
goo s = set s 66 10


{-@ foo :: s:State -> { s1:State | get s1 "x" == 10 } @-}
foo :: State -> State  
foo s = set s "x" 10

{-@ bar :: s:State -> { get (set s "x" 10)  "x" == 10 } @-}
bar :: State -> () 
bar s = ()

