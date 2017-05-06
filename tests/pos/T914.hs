{-@ LIQUID "--higherorder" @-}

module MapFusion where

import Language.Haskell.Liquid.ProofCombinators

{-@ inline compose @-}

{-@ compose :: f:(b -> c) -> g:(a -> b) -> x:a -> c @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
