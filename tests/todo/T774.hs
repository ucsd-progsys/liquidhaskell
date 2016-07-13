
-- | Why does this NOT fail?! Clearly there is a sort error?!

module LiquidR where

{-@ measure goober :: String -> Int @-}

{-@ incr :: x:Int -> {v:Bool | goober x == goober x} @-}
incr :: Int -> Bool
incr = undefined
