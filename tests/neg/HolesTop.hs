module HolesTop where

import Language.Haskell.Liquid.Prelude

{-@ foo :: _ -> Bool @-}
foo = liquidAssertB

bar = foo True
