--{-# LANGUAGE RankNTypes #-}
--{-@ LIQUID "--reflection" @-}
--{-@ LIQUID "--ple" @-}
-- module Data.Foldable.Classes where
import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                , foldr
                                                , head
                                                , flip
                                                , tail
                                                , Maybe (..)
                                                , Foldable (..)
                                                , id
                                                )

import Data.Semigroup.Classes
import Liquid.ProofCombinators
import Data.Endo
import Data.Functor.Identity
import Data.Dual
import Data.Function
import Data.List
import Data.List.NonEmpty
import Data.Maybe
import Data.Functor.Const

{-@ reflect composeEndo @-}
composeEndo :: (b -> a -> a) -> b -> Endo a
composeEndo f x = Endo (f x)

{-@ reflect dualEndoFlip @-}
dualEndoFlip :: (a -> b -> a) -> b -> Dual (Endo a)
dualEndoFlip f x  = Dual (Endo (flip f x))


instance Semigroup (Endo a) where
  mappend (Endo f) (Endo g) = Endo (compose f g)
  sconcat (NonEmpty h t) = foldlList mappend h t


-- instance VSemigroup (Endo a) where
--   lawAssociative (Endo f) (Endo g) (Endo h) = composeAssoc f g h `cast` ()
--   lawSconcat (NonEmpty h t) = sconcat (NonEmpty h t) `cast` ()

instance Monoid (Endo a) where
  mempty = Endo id
  mconcat = foldrList mappend mempty

-- instance VMonoid (Endo a) where
--   lawEmpty (Endo f) = composeId f
--   lawMconcat _ = ()






-- data Complex a = Complex a a

-- instance Foldable Complex where
--   foldMap f (Complex a b) = f a `mappend` f b
--   foldr f m (Complex a b) = f a (f b m)

-- instance VFoldable Complex where
--   lawFoldable1 _ _ _ = ()

