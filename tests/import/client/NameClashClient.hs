module NameClashClient where

import qualified NameClashLib as Lib 

data Foo = FooClient Int

{-@ bar :: Lib.FooAlias -> Nat @-}
bar :: Lib.Foo -> Int 
bar _ = 20 

baz = Lib.foo
