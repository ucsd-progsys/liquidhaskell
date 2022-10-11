module AssumedRecursive where

{-@ lazy foo @-}
{-@ assume foo :: a -> a @-}
foo :: a -> a
foo f = foo f
