-- see https://github.com/ucsd-progsys/liquidhaskell/issues/1074

module Blank where

{-@ type Geq X = {v:Int | X <= v} @-}

{-@ thisOk :: x:Int -> y:{Int | y > 10}  -> () @-}
thisOk :: Int -> Int -> ()
thisOk = undefined

{-@ thisBad1 :: x:Int -> y:Geq y  -> () @-}
thisBad1 :: Int -> Int -> ()
thisBad1 = undefined

{-@ thisBad2 :: x:Int -> y:{y > 10}  -> () @-}
thisBad2 :: Int -> Int -> ()
thisBad2 = undefined

{-@ type NEList a = {xs:[a] | len xs > 0} @-}

{-@ the3 :: Eq a => xs:NEList {x:a | x == headP xs} -> {y:a | headP xs == y} @-}
the3 :: Eq a => [a] -> a
the3 = undefined

{-@ the1 :: Eq a => xs:NEList {x:a | x == headP xs} -> {y:a | headP xs == y} @-}
the1 :: Eq a => [a] -> a
the1 = undefined

{-@ the2 :: Eq a => xs:{v:[{x:a | x == headP xs}] | len v > 0} -> {y:a | headP xs == y} @-}
the2 :: Eq a => [a] -> a
the2 = undefined

{-@ measure headP :: a -> b @-}

