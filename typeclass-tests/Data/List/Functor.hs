{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.List.Functor where
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
import Data.List
import Data.Functor.Classes
import Liquid.ProofCombinators
import Data.Function


{-@ apDistrib :: f:List (a -> b) -> g:List (a -> b) -> xs:List a -> {ap (appendL f g) xs == appendL (ap f xs) (ap g xs)}  @-}
apDistrib :: List (a -> b) -> List (a -> b) -> List a -> ()
apDistrib Nil _ _ = ()
apDistrib fs@(Cons f fs') gs xs =
  apDistrib fs' gs xs `cast` appendLAssoc (fmap f xs) (ap fs' xs) (ap gs xs)

{-@ fmapResAppend :: f:(a -> b) -> xs:List a -> ys:List a -> {fmap f (appendL xs ys) == appendL (fmap f xs) (fmap f ys)} @-}
fmapResAppend :: (a -> b) -> List a -> List a -> ()
fmapResAppend f Nil         ys = ()
fmapResAppend f (Cons _ xs) ys = fmapResAppend f xs ys

{-@ lawfListList :: f:(b -> c) -> gs: List (a -> b) -> as:List a -> {fmap f (ap gs as) == ap (fmap (compose f) gs) as } @-}
lawfListList :: (b -> c) -> List (a -> b) -> List a -> ()
lawfListList f Nil xs = ()
lawfListList f (Cons g gs) xs =
  fmapResAppend f (fmap g xs) (ap gs xs)
    `cast` lawfListList f gs xs
    `cast` lawFunctorComposition f g xs


{-@ listBindDistrib :: xs:List a -> ys:List a -> f:(a -> List b) -> {appendL (bind xs f) (bind ys f) == bind (appendL xs ys) f} @-}
listBindDistrib :: List a -> List a -> (a -> List b) -> ()
listBindDistrib (Cons x xs) ys f =
  appendLAssoc (f x) (bind xs f) (bind ys f) `cast` listBindDistrib xs ys f
listBindDistrib _ _ _ = ()

instance Functor List where
  fmap _ Nil         = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)
  y <$ Nil         = Nil
  y <$ (Cons x xs) = Cons y (y <$ xs)

instance VFunctor List where
  lawFunctorId Nil         = ()
  lawFunctorId (Cons _ xs) = lawFunctorId xs
  lawFunctorComposition _ _ Nil         = ()
  lawFunctorComposition f g (Cons _ xs) = lawFunctorComposition f g xs


instance Applicative List where
  pure x = Cons x Nil
  ap Nil         _  = Nil
  ap (Cons f fs) xs = fmap f xs `appendL` ap fs xs
  liftA2 f x y = pure f `ap` x `ap` y
  a1 *> a2 = ap (id <$ a1) a2
  a1 <* a2 = liftA2 const a1 a2




instance VApplicative List where
  lawApplicativeId Nil         = ()
  lawApplicativeId (Cons x xs) = lawApplicativeId xs

  lawApplicativeComposition Nil (Cons g gs) (Cons x xs) = ()
  lawApplicativeComposition (Cons f fs) v w =
    appendLNil (fmap compose (Cons f fs))
      `cast` apDistrib (fmap (compose f) v) (ap (fmap compose fs) v) w
      `cast` lawApplicativeComposition fs v w
      `cast` lawfListList f v w
      `cast` ()

  lawApplicativeComposition _ _ _ = ()
  lawApplicativeHomomorphism f x _ = appendLNil (fmap f (Cons x Nil))
  lawApplicativeInterchange Nil _ = ()
  lawApplicativeInterchange (Cons u us) y =
    lawApplicativeInterchange us y
      `cast` appendLNil (fmap (flip apply y) us)
      `cast` appendLNil (fmap (flip apply y) (Cons u us))
      `cast` ()

instance Monad List where
  bind Nil         f = Nil
  bind (Cons x xs) f = f x `appendL` bind xs f
  return = pure
  mseq Nil         _  = Nil
  mseq (Cons _ xs) ys = ys `appendL` mseq xs ys


instance VMonad List where
  lawMonad1 x f = appendLNil (f x)
  lawMonad2 Nil         = ()
  lawMonad2 (Cons _ xs) = lawMonad2 xs
  lawMonad3 Nil f g h = ()
  lawMonad3 (Cons x xs) f g h =
    listBindDistrib (f x) (bind xs f) g
      `cast` lawMonad3 xs f g h
      `cast` h x
      `cast` ()
  lawMonadReturn _ _ = ()
