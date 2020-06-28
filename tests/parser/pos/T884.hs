module T884 where

{-@ isEmpty :: x:[Int] -> {v:Bool | v <=> len x == 0} @-}
isEmpty :: [Int] -> Bool
isEmpty []    = True
isEmpty (_:_) = False
