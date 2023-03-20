{-@ LIQUID "--relational-hint" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module RVar where

{-@ measure RVar.x1 :: Int @-}
{-@ measure RVar.x2 :: Int @-}
x1, x2 :: Int
x1 = 0
x2 = 1

{-@ reflect y1 @-}
{-@ reflect y2 @-}
y1, y2 :: Int
y1 = x1
y2 = x2

--- Proof ---
{-@ assume relX1X2 :: {x1 <= x2} @-}
relX1X2 :: ()
relX1X2 = ()

{-@ relational y1 ~ y2 :: { Int ~ Int | r1 <= r2 } @-}
--- End ---