module SClass where

import qualified Data.Set

data Stack a = S [a]

data Foo a = F {stack :: Stack a}

{-@ class measure elts  :: forall f a. f a -> Data.Set.Set a @-}

{-@ measure  eltss :: [(Foo a)] -> (Data.Set.Set a)
    eltss([]) = {v| (? (Set_emp v))}
    eltss(x:xs) = (Set_cup (elts x) (eltss xs))
  @-}

