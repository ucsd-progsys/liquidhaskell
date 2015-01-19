{-@ LIQUID "--short-names"    @-}

module InlineMeasures where

{-@ measure mmax @-}
mmax       :: (Int, Int) -> Int
mmax (x,y) = if x > y then x else y

{-@ measure foo @-}
foo        :: [Int] -> Int
foo []     = 0
foo (x:xs) = if (x > 0) then x else 0 

{-@ measure bar @-}
bar        :: [Int] -> Int
bar []     = 0
bar (x:xs) = y + z where y = x
                         z = 10

{-@ measure llen @-}
llen        :: [a] -> Int
llen []     = 0
llen (x:xs) = 1 + z where z = llen xs

{-@ goo :: _ -> xs:_ -> {v:_ | llen v = llen xs } @-}
goo f []     = []
goo f (x:xs) = f x : goo f xs 
