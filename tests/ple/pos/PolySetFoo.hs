{-@ LIQUID "--reflection"     @-}

module PolySetFoo where

import Prelude hiding (last)

{-@ reflect last @-}
{-@ last :: xs:{ [a] | len xs > 0 } -> a @-}
last :: [a] -> a
last [x]      = x
last (_ : xs) = last xs

data Foo t = Foo1
  deriving (Eq, Ord)

{-@ reflect isFoo @-}
isFoo :: Foo t -> Bool
isFoo Foo1 = True

{-@ reflect foos @-}
{-@ foos :: Foo t -> [{ v:Foo t | isFoo v }] @-}
foos :: Foo t -> [Foo t]
foos f = if isFoo f then f : [] else []
