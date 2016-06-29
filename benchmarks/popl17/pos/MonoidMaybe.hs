{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module MonoidMaybe where

import Prelude hiding (Maybe(..), mappend, mempty)

import Proves
import Helper

-- | Monoid
-- | mempty-left ∀ x . mappend mempty  x ≡ x
-- | mempty-right ∀ x . mappend x  mempty ≡ x
-- | mappend-assoc ∀ x y z . mappend (mappend x  y) z ≡ mappend x (mappend y z)


{-@ axiomatize mempty @-}
mempty :: Maybe a
mempty = Nothing


{-@ axiomatize mappend @-}
mappend :: Maybe a -> Maybe a -> Maybe a
mappend Nothing y
  = y
mappend (Just x) y
  = Just x

mempty_left :: Maybe a -> Proof
{-@ mempty_left :: x:Maybe a -> { mappend mempty x == x }  @-}
mempty_left x
  =   mappend mempty x
  ==! mappend Nothing x
  ==! x
  *** QED

mempty_right :: Maybe a -> Proof
{-@ mempty_right :: x:Maybe a -> { mappend x mempty == x }  @-}
mempty_right Nothing
  =   mappend Nothing mempty
  ==! mempty
  ==! Nothing
  *** QED

mempty_right (Just x)
  = mappend (Just x) mempty
  ==! mappend (Just x) Nothing
  ==! Just x
  *** QED

{-@ mappend_assoc :: xs:Maybe a -> ys:Maybe a -> zs:Maybe a
                  -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } @-}
mappend_assoc :: Maybe a -> Maybe a -> Maybe a -> Proof
mappend_assoc (Just x) y z
  =   mappend (mappend (Just x) y) z
  ==! mappend (Just x) z
  ==! Just x
  ==! mappend (Just x) (mappend y z)
  *** QED
mappend_assoc Nothing (Just y) z
  =   mappend (mappend Nothing (Just y)) z
  ==! mappend (Just y) z
  ==! Just y
  ==! mappend (Just y) z
  ==! mappend Nothing (mappend (Just y) z)
  *** QED
mappend_assoc Nothing Nothing z
  =   mappend (mappend Nothing Nothing) z
  ==! mappend Nothing z
  ==! mappend Nothing (mappend Nothing z)
  *** QED

data Maybe a = Nothing | Just a
{-@ data Maybe a = Nothing | Just a @-}
