-- | Right now this gives a rather mysterious error, 
--   cannot unify `int` with `(a b)` it would be nice 
--   to actually point out the offending sub-expression, namely `len x`.

module LiquidR where

{-@ measure goober :: String -> Int @-}

{-@ incr :: x:Int -> {v:Bool | goober x == 0} @-}
incr :: Int -> Bool
incr = undefined
