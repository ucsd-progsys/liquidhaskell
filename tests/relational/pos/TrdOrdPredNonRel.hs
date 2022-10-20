module TrdOrdPredNonRel where

{-@ reflect h @-}
h :: Int -> Int
h x = x + 1

{-@ reflect g @-}
g :: (Int -> Int) -> Int
g h = h 0 

f :: ((Int -> Int) -> Int) -> Int
f g = g h

{-@ relational f ~ f :: g1:(h1:(x1:Int -> Int) -> Int) -> Int 
                      ~ g2:(h2:(x2:Int -> Int) -> Int) -> Int 
                     | ((x1 < x2 => r1 x1 < r2 x2) => r1 h1 < r2 h2) => r1 g1 < r2 g2 @-}