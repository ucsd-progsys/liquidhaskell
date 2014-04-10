module Zoo where

import Language.Haskell.Liquid.Prelude

data L a = C a (L a) | N | C2 a a (L a)

bob (C x _) = x
bob _       = liquidError "asdasd"
