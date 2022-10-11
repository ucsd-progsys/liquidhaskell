{-@ LIQUID "--expect-any-error" @-}
module NoExhaustiveGuardsError where

bar :: Int -> Int -> Int
bar x y | x >  y = 1
        | x == y = 0
