module MeasureBug where

data Heap a   = Empty | Node { pri   :: a
                             , rnk   :: Int 
                             , left  :: Heap a
                             , right :: Heap a
                             }


{-@ measure zoo @-}
zoo (Empty)        = 0
zoo (Node _ _ l r) = 1 + zoo l + zoo r
