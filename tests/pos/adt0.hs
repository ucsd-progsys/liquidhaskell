module Adt () where

import Language.Haskell.Liquid.Prelude

data Pair a = P a Int | D a Bool


goo z = P z z

baz = goo 10
