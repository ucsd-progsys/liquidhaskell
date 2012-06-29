module Deptup0 where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: a -> b -> Bool> = P (x :: a) (y :: b<p x>) @-} 

data Pair a b = P a b

mkPair x y = P x y

incr :: Int -> Int 
incr x = x + 1

baz x  = mkPair x (incr x)

bazList  xs = map baz xs

n           = choose 0

xs          = [0,1,2,3,4]

prop_baz    = map chk $ bazList xs 

chk :: (Pair Int Int) -> Bool
chk (P x y) = assert (x < y)

