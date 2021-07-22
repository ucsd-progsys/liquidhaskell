{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--aux-inline" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Reader.Functor where
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
import Data.Function
import Data.Reader
import Data.Functor.Classes


{-@ reflect fmapReader @-}
fmapReader :: (a -> b) -> (r -> a) -> r -> b
fmapReader f x r = f (x r)

{-@ fmapReaderId :: f:(r -> a) -> {fmapReader id f == id f}  @-}
fmapReaderId :: (r -> a) -> ()
fmapReaderId f =
  axiomExt (fmapReader id f) (id f) $ \r -> fmapReader id f r `cast` ()

{-@ lawFunctorCompositionReader :: f:(b -> c) -> g:(a -> b) -> x:(r -> a) -> {fmapReader (compose f g) x == compose (fmapReader f) (fmapReader g) x} @-}
lawFunctorCompositionReader :: (b -> c) -> (a -> b) -> (r -> a) -> ()
lawFunctorCompositionReader f g x =
  axiomExt (fmapReader (compose f g) x)
           (compose (fmapReader f) (fmapReader g) x)
    $ \s ->
        let c   = fmapReader (compose f g) x s
            c'  = compose (fmapReader f) (fmapReader g) x s
            c'' = x s
        in  ()

{-@ reflect apReader @-}
apReader :: (r -> a -> b) -> (r -> a) -> r -> b
apReader f x r = f r (x r)


{-@ lawApplicativeIdReader :: v:(r -> a) -> r:r -> {apReader (const id) v r == v r } @-}
lawApplicativeIdReader :: (r -> a) -> r -> ()
lawApplicativeIdReader v x = apReader (const id) v x `cast` ()

{-@ lawApplicativeCompositionReader :: u: (r -> b -> c) -> v: (r -> a -> b) -> w: (r -> a) -> r:r ->  {apReader (apReader (apReader (const compose) u) v) w r = apReader u (apReader v w) r} @-}
lawApplicativeCompositionReader
  :: (r -> b -> c) -> (r -> a -> b) -> (r -> a) -> r -> ()
lawApplicativeCompositionReader u v w r = ()

{-@ lawApplicativeHomomorphismReader :: g:(a -> b) -> x:a -> {px: (r -> a) | px = const x} -> r:r -> {apReader (const g) px r = const (g x) r} @-}
lawApplicativeHomomorphismReader :: (a -> b) -> a -> (r -> a) -> r -> ()
lawApplicativeHomomorphismReader g x px r =
  const x r `cast` apReader (const g) px r `cast` px r `cast` ()

{-@ lawApplicativeInterchangeReader :: u: (r -> a -> b) -> y:a -> r:r -> {apReader u (const y) r = apReader (const (flip apply y)) u r} @-}
lawApplicativeInterchangeReader :: (r -> a -> b) -> a -> r -> ()
lawApplicativeInterchangeReader u y r = ()




instance Functor (Reader r) where
  fmap f (Reader x) = Reader (fmapReader f x)
  (<$) a _ = Reader $ \r -> a

instance VFunctor (Reader r) where
  lawFunctorId (Reader f) = fmapReaderId f
  lawFunctorComposition f g (Reader x) = lawFunctorCompositionReader f g x


instance Applicative (Reader r) where
  pure x = Reader (const x)
  ap (Reader f) (Reader a) = Reader (apReader f a)
  liftA2 f x y = pure f `ap` x `ap` y
  a1 *> a2 = ap (id <$ a1) a2
  a1 <* a2 = liftA2 const a1 a2

instance VApplicative (Reader r) where
  lawApplicativeId (Reader v) =
    axiomExt (apReader (const id) v) v (lawApplicativeIdReader v)
  lawApplicativeComposition (Reader u) (Reader v) (Reader w) = axiomExt
    (apReader (apReader (apReader (const compose) u) v) w)
    (apReader u (apReader v w))
    (lawApplicativeCompositionReader u v w)
  lawApplicativeHomomorphism g x (Reader px) = axiomExt
    (apReader (const g) px)
    (const (g x))
    (lawApplicativeHomomorphismReader g x px)
  lawApplicativeInterchange (Reader u) y = axiomExt
    (apReader u (const y))
    (apReader (const (flip apply y)) u)
    (lawApplicativeInterchangeReader u y)
