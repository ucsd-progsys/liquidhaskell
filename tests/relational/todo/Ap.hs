module Fixme where

{-@ reflect ap @-}
ap :: (Int -> Int) -> Int -> Int
ap f x = f x

{-@ thm :: f1:(Int -> Int) -> x1:Int -> {ap f1 x1 = ap f1 x1} @-}
thm :: (Int -> Int) -> Int -> ()
thm _ _ = ()

{-@ relational ap ~ ap :: { f1:_ -> xs1:_ -> _ 
                          ~ f2:_ -> xs2:_ -> _ 
                          | f1 = f2
                            :=> xs1 = xs2 
                            :=> r1 f1 xs1 = r2 f2 xs2 } @-}
