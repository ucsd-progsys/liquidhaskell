{-@ LIQUID "--modern" @-}

module T2652 where

{-@ reflect f @-}
f :: Int -> Int
f x = if x >= 0 then x else x

{-@ reflect g @-}
g :: Int -> Int
g x = if x <= 0 then x else x

{-@ test :: { f = g } @-}
test :: ()
test = ()
