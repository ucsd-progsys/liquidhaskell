module Foo where

{-@ data Foo = F { thing :: Nat } @-}
data Foo = F { thing :: Int }


{-@ bar :: Foo -> Nat @-}
bar z = thing z


