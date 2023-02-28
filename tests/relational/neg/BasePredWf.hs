{-@ LIQUID "--expect-any-error" @-}
module BasePredWf where

abs :: Int -> Int
abs x = if x < 0 then -x else x

{-@ relational abs ~ abs :: { x1:Int -> Int 
                            ~ x2:Int -> Int
                            | r1 x1 < r2 x2 } @-}
