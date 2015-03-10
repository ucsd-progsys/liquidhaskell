module BadExprArg where

{-@ type ListN a N = {v:[a] | len v = N} @-}

{-@ foo :: ListN 0 0 @-}
foo :: [a]
foo = undefined
