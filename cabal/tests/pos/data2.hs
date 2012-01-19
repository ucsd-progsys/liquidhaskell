module Range where

import Control.Applicative
import Language.Haskell.Liquid.Prelude

data LL a = N | C { head :: a, tail :: (LL a) }

--instance Functor LL where
--  fmap f N                = N
--  fmap f (C jhala jhalas) = C (f jhala) (fmap f jhalas)

incr x = x + 1

lmap f N = N
lmap f (C jhala jhalas) = C (f jhala) (lmap f jhalas)

range :: Int -> Int -> LL Int
range i j = C i N

prop_rng1 n   = (assert . (0 <=)) `lmap` range 0 n
