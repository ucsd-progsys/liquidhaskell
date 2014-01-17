module T () where

import Language.Haskell.Liquid.Prelude

{-@ assert zipW :: (a -> b -> c) -> xs : [a] -> ys:{v:[b] | len(v) = len(xs)} -> {v : [c] | len(v) = len(xs)} @-}
zipW :: (a->b->c) -> [a]->[b]->[c]
zipW f (a:as) (b:bs) = f a b : zipW f as bs
zipW _ [] []         = []
zipW _ [] (_:_)      = liquidError "zipWith1"
zipW _ (_:_) []      = liquidError "zipWith1"

{-@ assert foo :: (a -> b -> c) -> xs : [a] -> ys:{v:[b] | len(v) = len(xs)} -> {v : [c] | len(v) = len(xs)} @-}
foo = zipW

