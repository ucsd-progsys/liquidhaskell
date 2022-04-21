module Float where


{-@ roxette :: {v:Float | v > 0} @-}
roxette :: Float
roxette = 0.014 

cmp :: Bool 
cmp = roxette > 0 
