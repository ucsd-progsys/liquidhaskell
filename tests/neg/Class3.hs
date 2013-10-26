{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}
module Class where

import Language.Haskell.Liquid.Prelude
import Prelude hiding (sum, length, (!!), Functor(..))
import qualified Prelude as P

{-@ qualif Sz(v:int, xs:a): v = (sz xs) @-}

{-@ data List a = Nil | Cons (hd::a) (tl::(List a)) @-}
data List a = Nil | Cons a (List a)


{-@ class measure sz :: forall a. a -> Int @-}
{-@ class Sized s where
      size :: forall a. x:s a -> {v:Nat | v = (sz x)}
  @-}
class Sized s where
  size :: s a -> Int

instance Sized List where
  {-@ instance measure sz :: List a -> Int
      sz (Nil)       = 0
      sz (Cons x xs) = 1 + (sz xs)
    @-}
  size Nil         = 0
  size (Cons x xs) = size xs



