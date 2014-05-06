module SClass where

import qualified Data.Set

data Stack a = S [a]

data Foo a = F {stack :: Stack a}

{-@ class measure elts  :: a -> Data.Set.Set a @-}

{-@ instance measure elts :: Stack a -> (Data.Set.Set a)
    elts (S xs) = (listElts xs)
  @-}

{-@ instance measure elts :: Foo a -> (Data.Set.Set a)
    elts (F st) = (elts st)
  @-}

{-@ measure bad :: [Foo a] -> (Data.Set.Set a)
    bad([]) = {v| (? (Set_emp v))}
    bad(x:xs) = (elts x)
  @-}
