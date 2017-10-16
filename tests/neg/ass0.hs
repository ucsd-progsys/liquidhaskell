module Ass (testError) where

-- import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ assert foo :: x:a -> {v: a | (v != x) } @-}
foo x = x 

testError :: Int -> Int 
testError x = bar x 


{-@ bar :: Nat -> Nat @-} 
bar :: Int -> Int 
bar x = x