module spec Data.Foldable where

import Data.List

assume length :: Data.Foldable.Foldable f => xs:f a -> {v:Nat | v = flen xs}

class measure flen :: forall f a. f a -> Int

instance measure flen :: [a] -> Int
flen [] = 0
flen (x:xs) = 1 + flen xs

invariant {v:f a | 0 <= flen v}
invariant {v:[a] | len v = flen v}

