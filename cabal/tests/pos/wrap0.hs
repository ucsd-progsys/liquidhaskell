module Wrap0 where

import Language.Haskell.Liquid.Prelude (liquidError, liquidAssertB)

data WrapTypeGen b a = WrapType {getVect :: b, getVal :: a}

type WrapType a      = WrapTypeGen [Double] a

instance Eq (WrapType a) where
   (==) = (==) `on` getVect

instance Ord (WrapType a) where
    compare = comparing getVect
{-@ data Foo a <p :: a -> Bool> = F (f :: a <p>) @-}
data Foo a = F a

type IntFoo = Foo Int

{-@ assert flibberty :: (Eq a) => a -> Bool @-}
flibberty x   = prop x (F x)
prop x (F y)  = liquidAssertB (x == y)

{-@ assert flibInt :: (Num a, Ord a) => a -> Bool @-}
flibInt x     = prop1 x (F (x + 1))
prop1 x (F y) = liquidAssertB (x < y) 

{-@ assert flibXs :: a -> Bool @-}
flibXs x     = prop2 (F [x, x, x])
prop2 (F _)  = liquidError "no!"
prop2 (F _ ) = True
