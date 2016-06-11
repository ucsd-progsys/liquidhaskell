
module Language.Haskell.HsColour.General(
    dropLast, dropFirst, liquidAssume
    ) where


{-@ LIQUID "--totality" @-}

dropLast :: Eq a => a -> [a] -> [a]
dropLast x [y] | x == y = []
dropLast x (y:ys) = y : dropLast x ys
dropLast x [] = []


dropFirst :: Eq a => a -> [a] -> [a]
dropFirst x (y:ys) | x == y = ys
dropFirst x ys = ys

{-@ liquidAssume :: b:Bool -> x:a -> {v:a | ((Prop b) && (x = v))} @-}
liquidAssume     :: Bool -> a -> a
liquidAssume b x | b         = x
             | otherwise = error $ show b
