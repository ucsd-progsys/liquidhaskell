{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Functor.State.Functor where

import Prelude hiding (id, Functor(..))
import Data.Functor.State
import Data.Functor.Classes
import Liquid.ProofCombinators
import Data.Function


{-@ reflect fmapState @-}
fmapState :: (a -> b) -> (s -> (a, s)) -> s -> (b, s)
fmapState f h s = let (a, s') = h s in (f a, s')


{-@ fmapStateId :: f:(s -> (a,s)) -> {fmapState id f == id f}  @-}
fmapStateId :: (s -> (a, s)) -> ()
fmapStateId f = axiomExt (fmapState id f) (id f) $ \s ->
  let (a , s' ) = f s
      (a', s'') = fmapState id f s
  in  id a `cast` id a' `cast` ()

{-@ lawFunctorCompositionState :: f:(b -> c) -> g:(a -> b) -> x:(s -> (a,s)) -> {fmapState (compose f g) x == compose (fmapState f) (fmapState g) x} @-}
lawFunctorCompositionState :: (b -> c) -> (a -> b) -> (s -> (a, s)) -> ()
lawFunctorCompositionState f g x =
  axiomExt (fmapState (compose f g) x) (compose (fmapState f) (fmapState g) x)
    $ \s ->
        let (c , s'  ) = fmapState (compose f g) x s
            (c', s'' ) = compose (fmapState f) (fmapState g) x s
            (a , s''') = x s
        in  ()

instance Functor (State s) where
  fmap f (State g) = State (fmapState f g)
  a <$ (State f) = State $ \s -> let (_, s') = f s in (a, s')

instance VFunctor (State s) where
  lawFunctorId (State f) = fmapStateId f `cast` ()
  lawFunctorComposition f g (State h) =
    lawFunctorCompositionState f g h `cast` ()
