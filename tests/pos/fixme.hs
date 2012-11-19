module Test where

{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}

{-@ choo :: OList a -> OList a @-}
choo (x:xs) = let z = x:xs in z
