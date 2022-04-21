{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MonoidMaybe where

import Prelude hiding (mappend, mempty)

import Language.Haskell.Liquid.ProofCombinators

-- | Monoid
-- | mempty-left ∀ x . mappend mempty  x ≡ x
-- | mempty-right ∀ x . mappend x  mempty ≡ x
-- | mappend-assoc ∀ x y z . mappend (mappend x  y) z ≡ mappend x (mappend y z)


{-@ reflect mempty @-}
mempty :: Maybe a
mempty = Nothing


{-@ reflect mappend @-}
mappend :: Maybe a -> Maybe a -> Maybe a
mappend Nothing y
  = y
mappend (Just x) y
  = Just x

mempty_left :: Maybe a -> Proof
{-@ mempty_left :: x:Maybe a -> { mappend mempty x == x }  @-}
mempty_left _ = trivial 

mempty_right :: Maybe a -> Proof
{-@ mempty_right :: x:Maybe a -> { mappend x mempty == x }  @-}
mempty_right Nothing
  = trivial

mempty_right (Just x)
  = trivial

{-@ mappend_assoc :: xs:Maybe a -> ys:Maybe a -> zs:Maybe a
                  -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } @-}
mappend_assoc :: Maybe a -> Maybe a -> Maybe a -> Proof
mappend_assoc (Just x) y z
  =   trivial
mappend_assoc Nothing (Just y) z
  =   trivial
mappend_assoc Nothing Nothing z
  =   trivial

