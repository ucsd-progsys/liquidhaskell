module Wrap0 () where

import Language.Haskell.Liquid.Prelude (liquidError, liquidAssertB)

data Foo a = F a

type IntFoo = Foo Int

{-@ flibberty :: (Eq a) => a -> Bool @-}
flibberty x   = prop x (F x)
prop x (F y)  = liquidAssertB (x == y)

{-@ flibInt :: (Num a, Ord a) => a -> Bool @-}
flibInt x     = prop1 x (F (x + 1))
prop1 x (F y) = liquidAssertB (x < y) 

{-@ flibXs :: a -> Bool @-}
flibXs x     = prop2 (F [x, x, x])
prop2 (F []) = liquidError "not-the-hippopotamus"
prop2 (F _ ) = True
