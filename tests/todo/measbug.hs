module MeasureBug where

data Heap a   = Empty | Node { pri   :: a
                             , rnk   :: Int 
                             , left  :: Heap a
                             , right :: Heap a
                             }
{-@ data Heap [zoo] @-}

{-@ invariant {v:Heap a| (zoo v) >=0} @-}

{-@ measure zoo @-}
zoo :: Heap a -> Int
zoo (Empty)        = 0
zoo (Node _ _ l r) = 1 + zoo l + zoo r
