{-@ LIQUID "--typed-holes" @-}

module T2402 where

import Language.Haskell.Liquid.Synthesize.Error

{-@ foo :: x: a -> ( { v: [a] | len v == 1 }, { v: [a] | len v == 0 } ) @-}
foo :: a -> ([a], [a])
foo = _goal
-- foo x = ([x], [])
