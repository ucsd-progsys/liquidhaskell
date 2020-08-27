{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

data Lis = LNil | LCons Int Lis


{-@ reflect length' @-}
{-@ length' :: Lis -> {v:Int | 0 <= v } @-}
length' :: Lis -> Int
length' LNil          = 0
length' (LCons _ xxs) = 1 + length' xxs

{-@ type ListX  X = {l:Lis | length' l == length' X } @-}

{-@ reflect zw @-}
{-@ zw ::  xs:Lis -> ListX xs -> ListX xs @-}
zw :: Lis -> Lis -> Lis
zw _    thelist@(LCons _ _) = thelist
zw LNil LNil                = LNil