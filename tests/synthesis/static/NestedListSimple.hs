{-@ LIQUID "--typed-holes" @-}

module NestedListSimple where

import Language.Haskell.Liquid.Synthesize.Error

{-@ foo :: { v: [[a]] | len v == 2} @-}
foo :: [[a]]
foo = (:) [] ((:) [] [])
