{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Functor where

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
import           Data.List
import Data.Function
import Data.Functor.Classes
-- TODO: Move these to a separate module. 



-- TODO: Define `Maybe a` in Data.Maybe



-- Kleisli Arrow



{-@ data Pair a b = Pair {projl :: a, projr :: b }  @-}
data Pair l r = Pair {projl :: l, projr :: r }
-- Writer Monad
instance Functor (Pair u) where
  fmap f (Pair u a) = (Pair u (f a))
  a <$ (Pair u _) = (Pair u a)

instance VFunctor (Pair u) where
  lawFunctorId (Pair _ _) = ()
  lawFunctorComposition _ _ _ = ()

-- instance Monoid u => Applicative (Pair u) where
--   pure x = Pair mempty x
--   ap (Pair u f) (Pair v x) = (Pair (u `mappend` v) (f x))
--   liftA2 f x y = pure f `ap` x `ap` y
--   a1 *> a2 = ap (id <$ a1) a2
--   a1 <* a2 = liftA2 const a1 a2

-- instance Monoid u => Monad (Pair u) where
--   bind (Pair u a) k = case k a of
--     (Pair v b) -> (Pair (mappend u v) b)
--   return = pure
--   mseq (Pair u _) (Pair v a) = (Pair (mappend u v) a)




-- instance (VMonoid u) => VApplicative (Pair u) where
--   lawApplicativeId _ = ()
--   lawApplicativeComposition (Pair _ _) (Pair _ _) (Pair _ _)  = ()
--   lawApplicativeHomomorphism f x (Pair _ _) = ()
--   lawApplicativeInterchange (Pair _ _) _ = ()



-- data Compose f g a = Compose {getCompose :: f (g a)}

-- instance (Functor f, Functor g) => Functor (Compose f g) where
--   fmap f (Compose x) = Compose $ fmap (fmap f) x
--   x <$ m = fmap (const x) m

-- instance (VFunctor f, VFunctor g) => VFunctor (Compose f g) where
-- --    {-@ lawFunctorId :: forall a . x:m a -> {fmap id x == id x} @-}
--   lawFunctorId (Compose x) =
--     (axiomExt (fmap id :: g a -> g a) id $ \x -> ()) `cast`
--     fmap id (Compose x) `cast`
--     fmap (fmap id) x `cast`
--     lawFunctorId x `cast`
--     ()
--   lawFunctorComposition f g (Compose x) =
--     fmap (fmap (compose f g)) x `cast`
--     ()

--    {-@ lawFunctorComposition :: forall a b c . f:(b -> c) -> g:(a -> b) -> x:m a -> { fmap (compose f g) x == compose (fmap f) (fmap g) x } @-}
--    lawFunctorComposition :: forall a b c. (b -> c) -> (a -> b) -> m a -> ()







-- Instantiation
-- {-@ optionCompose :: f:(a -> Optional b) -> g:(b -> Optional c) -> h:(c -> Optional d) -> x:a -> {kcompose (kcompose f g) h x == kcompose f (kcompose g h) x} @-}
-- optionCompose :: (a -> Optional b) -> (b -> Optional c) -> (c -> Optional d) -> a -> ()
-- optionCompose  = kcomposeAssoc 


-- -- TODO: Prove this
-- {-@ applicativeLemma1 :: VApplicative m => f:(a -> b) -> x:m a -> {fmap f x == ap (pure f) x} @-}
-- applicativeLemma1 :: VApplicative m => (a -> b) -> m a -> ()
-- applicativeLemma1 f x = ()

-- -- TODO: Prove this
-- {-@ applicativeLemma2 :: VApplicative m => f:(d -> c -> e) -> g:(a -> b -> c) -> p:_ -> {q:_ | p (q x y) = compose (f x) (g y)} -> {liftA2 p (liftA2 q u v) = compose (liftA2 f u) (liftA2 g v)} @-}
-- applicativeLemma2 :: VApplicative m => (d -> c -> e) -> (a -> b -> c) -> _ -> _ -> ()
-- applicativeLemma2 f g p q = undefined







