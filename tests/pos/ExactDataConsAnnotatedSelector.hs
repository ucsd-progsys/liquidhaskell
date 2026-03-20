{-@ LIQUID "--adt" @-}

module ExactDataConsAnnotatedSelector where

{-@ data Zig = Zonk { pig :: Int } @-}
data Zig = Zonk Int

{-@ prop :: z:Zig -> {v:Int | v = pig z} @-}
prop :: Zig -> Int
prop (Zonk n) = n
