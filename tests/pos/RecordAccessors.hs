module RecordAccessors where

{-@ data Foo = F { thing :: Nat } @-}
data Foo = F { thing :: Int }

{-@ bar :: Foo -> Nat @-}
bar = thing
