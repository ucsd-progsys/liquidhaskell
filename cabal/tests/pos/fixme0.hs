module Fixme0 where

import Language.Haskell.Liquid.Prelude

data Map a1 a2 a3 a4 a5 = Tip

{-@ assert insert :: (Ord a1) => a1 -> a2 -> a3 -> a4 -> a5 -> Map a1 a3 a5 a2 a3 @-}
insert :: Ord a1 => a1 -> a2 -> a3 -> a4 -> a5 -> Map a1 a3 a5 a2 a3
insert x1 x2 x3 x4 x5       = Tip

data Foo a = F a

{-@ assert flibberty :: (Eq a) => a -> Bool -> c@-}
flibberty x   = prop x (F x)
prop x (F y)  = liquidAssertB (x == y)
