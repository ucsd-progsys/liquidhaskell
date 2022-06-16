{-@ LIQUID "--expect-error-containing=Illegal type specification for `T773.incr`" @-}
-- | Right now this gives a rather mysterious error, 
--   cannot unify `int` with `(a b)` it would be nice 
--   to actually point out the offending sub-expression, namely `len x`.

module T773 where

{-@ measure goober :: String -> Int @-}

{-@ incr :: x:Int -> {v:Bool | goober x == 0} @-}
incr :: Int -> Bool
incr = undefined
