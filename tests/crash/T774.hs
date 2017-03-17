
-- | Why does this NOT fail?! Clearly there is a sort error?!

module LiquidR where

{-@ measure goober :: String -> Int @-}

{-@ incr :: x:Int -> y:Int -> {v:Bool | goober x == goober y} @-}
incr :: Int -> Int -> Bool
incr = undefined
