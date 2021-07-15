{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--auxinline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Successors.Functor where
import Data.Function
import Data.Successors
import Data.Functor.Classes
import           Liquid.ProofCombinators
import Data.List
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


{-@ fmapFGEq :: f:(a -> b) -> g:(a -> b) -> xs:List a -> (x:a -> {f x == g x}) -> {fmapList f xs == fmapList g xs} @-}
fmapFGEq :: (a -> b) -> (a -> b) -> List a -> (a -> ()) -> ()
fmapFGEq f g Nil h = ()
fmapFGEq f g (Cons x xs) h = h x `cast` fmapFGEq f g xs h


{-@ trivialEq0 :: x:a -> g:(a -> b) -> f:(b -> c) -> {compose (flip apply x) (compose (flip apply g) compose) f == flip apply (g x) f} @-}
trivialEq0 :: a -> (a -> b) -> (b -> c) -> ()
trivialEq0 _ _ _ = ()

{-@ trivialEq1 :: x:a -> f:(b -> c) -> g:(a -> b) -> {compose (flip apply x) (compose f) g == compose f (flip apply x) g} @-}
trivialEq1 :: a -> (b -> c) -> (a -> b) -> ()
trivialEq1 _ _ _ =()

instance Functor Succs where
  fmap f (Succs o s) = Succs (f o) (fmapList f s)
  y <$ (Succs _ s) = Succs y  (fmapList (const y) s)

instance VFunctor Succs where
  lawFunctorId (Succs _ xs) = fmapListId xs
  lawFunctorComposition f g (Succs _ xs)    = fmapListComposition f g  xs

instance Applicative Succs where
  pure x = Succs x Nil
  ap (Succs f fs) (Succs x xs) = Succs (f x) (fmapList (flip apply x) fs `appendL` fmapList f xs)
  liftA2 f x y = pure f `ap` x `ap` y
  a1 *> a2 = ap (id <$ a1) a2
  a1 <* a2 = liftA2 const a1 a2




instance VApplicative Succs where
  lawApplicativeId (Succs x xs)  = fmapListId xs `cast` ()
  lawApplicativeComposition fall@(Succs f fs) gall@(Succs g gs) xall@(Succs x xs) = 
    fmapListResAppend (flip apply x) (fmapList (flip apply g) (fmapList compose fs)) (fmapList (compose f) gs) `cast`
    fmapListComposition f g xs`cast`
    appendLAssoc (fmapList (flip apply x) (fmapList (flip apply g) (fmapList compose fs)))
      (fmapList (flip apply x) (fmapList (compose f) gs))
      (fmapList (compose f g) xs) `cast`
    fmapListComposition (flip apply x) (compose (flip apply g) compose) fs `cast`
    fmapListComposition (flip apply g) compose fs `cast`
    fmapFGEq (compose (flip apply x) (compose (flip apply g) compose)) (flip apply (g x))  fs (trivialEq0 x g) `cast`
    fmapListComposition (flip apply x) (compose f) gs `cast`
    fmapListComposition f (flip apply x) gs `cast`
    fmapFGEq (compose (flip apply x) (compose f)) (compose f (flip apply x))   gs (trivialEq1 x f) `cast`
    (fmapList (compose (flip apply x) (compose f)) gs ===
     fmapList (compose f (flip apply x)) gs) `cast`
    fmapListResAppend f (fmapList (flip apply x) gs) (fmapList g xs) `cast`
    ()
  lawApplicativeHomomorphism g  x (Succs y Nil) = ()
  lawApplicativeInterchange (Succs f fs) y = appendLNil (fmapList (flip apply y) fs) `cast` ()
