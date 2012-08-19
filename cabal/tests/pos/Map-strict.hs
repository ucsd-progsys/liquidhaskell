module Data.Map.Base (Map(..), singleton) where

data Map k a  = Bin {-# UNPACK #-} !Size !k a !(Map k a) !(Map k a)
              | Tip

type Size     = Int

{-@ 
  data Map k a <l :: root:k -> k -> Bool, r :: root:k -> k -> Bool>
       = Bin (sz    :: Size) 
             (key   :: k) 
             (value :: a) 
             (left  :: Map <l, r> (k <l key>) a) 
             (right :: Map <l, r> (k <r key>) a) 
       | Tip 
  @-}

{-@ type OMap k a = Map <{v:k | v < root}, {v:k | v > root}> k a @-}

{-@ singleton :: k -> a -> OMap k a @-}
singleton :: k -> a -> Map k a
singleton k x = Bin 1 k x Tip Tip
{-# INLINE singleton #-}


