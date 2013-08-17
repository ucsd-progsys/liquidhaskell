module Fixme where

data Map k a = Tip | Bin Int k a (Map k a) (Map k a)

insert :: Ord k => k -> a -> Map k a -> Map k a
insert = go
  where
    go :: Ord k => k -> a -> Map k a -> Map k a
    go kx x Tip = singleton kx x
    go kx x (Bin sz ky y l r) =
        case compare kx ky of
                  -- Bin ky y (go kx x l) r 
            LT -> balanceL ky y (go kx x l) r
            GT -> balanceR ky y l (go kx x r)
            EQ -> Bin sz kx x l r

singleton = undefined
balanceL = undefined
balanceR = undefined
