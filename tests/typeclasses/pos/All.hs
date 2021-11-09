{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--aux-inline" @-}
{-@ LIQUID "--ple" @-}
module All where


import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                , foldr
                                                , head
                                                , flip
                                                , tail
                                                , Maybe (..)
                                                , Foldable (..)
                                                )

{-@ data List a = Nil | Cons {lh::a, lt::List a} @-}
data List a = Nil | Cons a (List a)

{-@ reflect foldrList @-}
foldrList :: (a -> b -> b) -> b -> List a -> b
foldrList _ x Nil         = x
foldrList f x (Cons y ys) = f y (foldrList f x ys)

{-@ reflect foldlList @-}
foldlList :: (b -> a -> b) -> b -> List a -> b
foldlList _ x Nil         = x
foldlList f x (Cons y ys) = foldlList f (f x y) ys


{-@ data NonEmpty a = NonEmpty {neh::a, net:: (List a)} @-}
data NonEmpty a = NonEmpty a (List a)

{-@ reflect head' @-}
head' :: NonEmpty a -> a
head' (NonEmpty a _) = a

{-@ reflect tail' @-}
tail' :: NonEmpty a -> List a
tail' (NonEmpty _ t) = t


class Semigroup a where
    {-@ mappend :: a -> a -> a @-}
    mappend :: a -> a -> a
    sconcat :: NonEmpty a -> a

class Semigroup a => VSemigroup a where
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {mappend (mappend v v') v'' == mappend v (mappend v' v'')} @-}
    lawAssociative :: a -> a -> a -> ()

    {-@ lawSconcat :: ys:NonEmpty a -> {foldlList mappend (head' ys) (tail' ys) == sconcat ys} @-}
    lawSconcat :: NonEmpty a -> ()

class Semigroup a => Monoid a where
    {-@ mempty :: a @-}
    mempty :: a

    mconcat :: List a -> a

class (VSemigroup a, Monoid a) => VMonoid a where
    {-@ lawEmpty :: x:a -> {mappend x mempty == x && mappend mempty x == x} @-}
    lawEmpty :: a -> () -- JP: Call this lawIdentity?

    {-@ lawMconcat :: xs:List a -> {mconcat xs == foldrList mappend mempty xs} @-}
    lawMconcat :: List a -> ()



{-@ assoc4 :: VSemigroup a => x:a -> y:a -> z:a -> h:a -> {mappend x (mappend y (mappend z h)) == mappend (mappend  (mappend x y) z) h} @-}
assoc4 :: VSemigroup a => a -> a -> a -> a -> ()
assoc4 x y z h =
  () `const`
  mappend x (mappend y (mappend z h)) `const`
  lawAssociative y z h `const`
  mappend x (mappend (mappend y z) h) `const`
  lawAssociative x (mappend y z) h `const`
  mappend (mappend x (mappend y z)) h `const`
  lawAssociative x y z `const`
  mappend (mappend (mappend x y) z) h


data PNat = Z | S PNat

instance Semigroup PNat where
  mappend Z     n = n
  mappend (S m) n = S (mappend m n)

  sconcat (NonEmpty h t) = foldlList mappend h t

instance VSemigroup PNat where
  lawAssociative Z     _ _ = ()
  lawAssociative (S p) m n = lawAssociative p m n
  lawSconcat (NonEmpty h t) = ()

instance Monoid PNat where
  mempty = Z
  mconcat xs = foldrList mappend mempty xs

instance VMonoid PNat where
  lawEmpty Z     = ()
  lawEmpty (S m) = lawEmpty m
  lawMconcat _ = ()



instance Semigroup (List a) where
  mappend Nil l2 = l2
  mappend (Cons h l1) l2 = Cons h (mappend l1 l2)
  sconcat (NonEmpty h t) = foldlList mappend h t

instance VSemigroup (List a) where
  lawAssociative Nil y z = ()
  lawAssociative (Cons _ x) y z = lawAssociative x y z
  lawSconcat (NonEmpty h t) = ()

instance Monoid (List a) where
  mempty = Nil
  mconcat xs = foldrList mappend mempty xs

instance VMonoid (List a) where
  lawEmpty Nil = ()
  lawEmpty (Cons _ t) = lawEmpty t
  lawMconcat _ = ()
