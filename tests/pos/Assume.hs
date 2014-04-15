module Assume where

import Language.Haskell.Liquid.Prelude

{-@ assume foo :: {v:Bool | (Prop v)} @-}
foo = False

bar = liquidAssertB foo
