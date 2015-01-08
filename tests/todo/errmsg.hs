{-@ LIQUID "--short-names" @-}

module Goo where

{- the "error message" is garbled thanks to all the ill-formatted
   "Eq [Contravariant]" stuff. Can we remove it, or at least NOT show
   it when running in --short-names mode. -}

{-@ foo :: (Eq a) => x:a -> xs:[a] -> {v:Bool | Prop v <=> (member x (elems xs))} @-}
foo          :: (Eq a) => a -> [a] -> Bool
foo x (y:ys) = x == y || elem x ys
foo _ []     = False


