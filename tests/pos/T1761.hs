
module T1761 where

{-@ inline oneFunPred @-}
oneFunPred :: Int -> Bool
oneFunPred x = x == 1

{-@ type OneTyAlias a = {v:a | oneFunPred v} @-}

{-@ data One = One { field :: OneTyAlias Int }  @-}
data One = One Int
