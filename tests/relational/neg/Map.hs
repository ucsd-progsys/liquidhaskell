module Fixme where

import Prelude hiding (map)

map :: (Int -> Int) -> [Int] -> [Int]
map _ [] = []
map f (x:xs) = x : map f xs

{-@ relational map ~ map :: f1:(x1:_ -> _) -> xs1:_ -> _ ~ f2:(x2:_ -> _) -> xs2:_ -> _ 
                         ~~ f1 == f2 => true => r1 f1 xs1 == r2 f2 xs2 @-}
