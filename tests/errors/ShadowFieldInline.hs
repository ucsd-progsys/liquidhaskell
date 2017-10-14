{-@ LIQUID "--exactdc" @-}

module Range where

-- LH should give an error message that the field selectors `pig`
-- is shadowed and should be renamed.

{-@ data Zig = Zonk { pig :: Int } @-}
data Zig = Zonk Int 

{-@ prop :: z:Zig -> {v:Int | v = pig z} @-}
prop :: Zig -> Int
prop (Zonk n) = n

{-@ inline pig @-}
pig :: Int -> Int
pig a = a + 1
