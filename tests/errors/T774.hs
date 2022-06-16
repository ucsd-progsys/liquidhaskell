{-@ LIQUID "--expect-error-containing=Illegal type specification for `T774.incr`" @-}

-- | Why does this NOT fail?! Clearly there is a sort error?!

module T774 where

{-@ measure goober :: String -> Int @-}

{-@ incr :: x:Int -> y:Int -> {v:Bool | goober x == goober y} @-}
incr :: Int -> Int -> Bool
incr = undefined
