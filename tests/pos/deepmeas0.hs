{-@ LIQUID "--pruneunsorted" @-}
module DeepMeasure () where

import Language.Haskell.Liquid.Prelude (liquidError)
import Data.Set

{-@ measure getfst :: (a, b) -> a
    getfst (x, y) = x
  @-}

{-@ measure keys :: [(k, v)] -> (Set k) 
    keys ([])   = {v | Set_emp v }
    keys (x:xs) = {v | (v = (Set_cup (Set_sng (getfst x)) (keys xs))) }
  @-}

{-@ getKeys :: kvs:[(a, b)] -> {v:[a] | ((keys kvs) = (listElts v))} @-}
getKeys []           = [] 
getKeys ((x,_) : xs) = x : getKeys xs

{-@ klookup :: forall k v. (Eq k) => k:k -> {v: [(k, v)] | (Set_mem k (keys v))} -> v @-}

klookup k ((k',v):kvs)
  | k == k'          = v
  | otherwise        = klookup k kvs
klookup _ []         = liquidError "Never!"




