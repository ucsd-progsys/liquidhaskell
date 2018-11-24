module Semigroup where

import Prelude hiding (Semigroup(..), mappend)

class Semigroup a where
    mappend :: a -> a -> a

    {-@ lawAssociative 
     :: x : a
     -> y : a
     -> z : a
     -> {mappend (mappend x y) z = mappend x (mappend y z)}
     @-}
    lawAssociative :: a -> a -> a -> ()

instance Semigroup Int where
    mappend a b = a ^ b

    lawAssociative x y z = ()
