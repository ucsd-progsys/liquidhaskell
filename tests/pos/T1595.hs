
module T1595 where

{-@ LIQUID "--reflection" @-}

data Map k v = Tip | Map k v (Map k v)

{-@ reflect mapEmpty @-}
mapEmpty :: Map k v 
mapEmpty = Tip 


{-@
data MultiSet a = MultiSet {
    posMultiSet :: Map a {v:Integer | v > 0 }
  }
@-}
data MultiSet a = MultiSet {
    posMultiSet :: Map a Integer -- ^ Map for elements currently in the set.
  }


{-@ empty :: MultiSet a @-}
empty :: MultiSet a
empty = MultiSet mapEmpty
