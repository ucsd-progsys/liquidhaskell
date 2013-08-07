-- | Error Message Test: parse error in spec

module Err0 where

import Language.Haskell.Liquid.Prelude

{-@ qualif Zog(v:FooBar, x:FooBar): v = x + @-}

data FooBar = Foo Int


x = choose 0

prop_abs ::  Bool
prop_abs = if x > 0 then baz x else False

baz gooberding = liquidAssertB (gooberding >= 0)
