{-@ LIQUID "--typed-holes" @-}

module TupleListSimple where

import Language.Haskell.Liquid.Synthesize.Error

{-@ foo :: x: a -> ( { v: [a] | len v == 1 }, { v: [a] | len v == 0 } ) @-}
foo :: a -> ([a], [a])
foo x_S0 = ((:) x_S0 [], [])