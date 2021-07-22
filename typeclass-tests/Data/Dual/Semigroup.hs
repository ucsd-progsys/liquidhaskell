{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Dual.Semigroup where
import           Prelude                 hiding ( Functor(..)
                                                , Applicative(..)
                                                , Monad(..)
                                                , Foldable(..)
                                                , Maybe(..)
                                                , Monoid(..)
                                                , Semigroup(..)
                                                , Either(..)
                                                , id
                                                , flip
                                                , const
                                                , apply
                                                )
import           Liquid.ProofCombinators
import Data.Dual
import Data.Semigroup.Classes
import Data.List.NonEmpty
import Data.List

instance Semigroup a => Semigroup (Dual a) where
  mappend (Dual v) (Dual v') = Dual (mappend v' v)
  sconcat (NonEmpty h t) = foldlList mappend h t

instance Monoid a => Monoid (Dual a) where
  mempty = Dual mempty
  mconcat xs = foldrList mappend mempty xs

instance VSemigroup a => VSemigroup (Dual a) where
  lawAssociative (Dual v) (Dual v') (Dual v'') = lawAssociative v'' v' v
  lawSconcat (NonEmpty h t) = sconcat (NonEmpty h t) `cast` ()

instance VMonoid a => VMonoid (Dual a) where
  lawEmpty (Dual v) = lawEmpty v
  lawMconcat xs = mconcat xs `cast` ()

-- Abstract Proof

{-@ dualdualHom :: Semigroup a => x:a -> y:a -> {mappend (Dual (Dual x)) (Dual (Dual y)) == Dual (Dual (mappend x y))} @-}
dualdualHom :: Semigroup a => a -> a -> ()
dualdualHom _ _ = ()

{-@ dualdualHom' :: Semigroup a => x:Dual (Dual a) -> y:Dual (Dual a) -> {getDual (getDual (mappend x y)) == mappend (getDual (getDual x)) (getDual (getDual y))} @-}
dualdualHom' :: Semigroup a => Dual (Dual a) -> Dual (Dual a) -> ()
dualdualHom' _ _ = ()
