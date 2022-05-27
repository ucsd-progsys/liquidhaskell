{-@ LIQUID "--noclasscheck"    @-}
module T385 where

import Prelude hiding (Functor, Monad)

data ST s a = ST {runState :: s -> (a,s)}

{-@ data ST s a <p :: s -> Bool, q :: s -> s -> Bool, r :: s -> a -> Bool> 
      = ST (runState :: x:s<p> -> (a<r x>, s<q x>)) @-}

{-@ runState :: forall <p :: s -> Bool, q :: s -> s -> Bool, r :: s -> a -> Bool>. ST <p, q, r> s a -> x:s<p> -> (a<r x>, s<q x>) @-}

class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor (ST s) where
  fmap f (ST g) = ST (\s -> let (a, s') = g s in (f a, s'))

class Functor m => Monad m where
  (>>) :: m a -> m b -> m b

instance Monad (ST s) where
  {-@ instance Monad ST s where
        >>  :: forall s a b  < pref :: s -> Bool, postf :: s -> s -> Bool
                    , pre  :: s -> Bool, postg :: s -> s -> Bool
                    , post :: s -> s -> Bool
                    , rg   :: s -> a -> Bool
                    , rf   :: s -> b -> Bool
                    , r    :: s -> b -> Bool
                    >. 
             {x::s<pre>, y::s<postg x> |- b<rf y> <: b<r x>}
             {xx::s<pre>, w::s<postg xx> |- s<postf w> <: s<post xx>}
             {ww::s<pre> |- s<postg ww> <: s<pref>}
             (ST <pre, postg, rg> s a)
          -> (ST <pref, postf, rf> s b)
          -> (ST <pre, post, r> s b)
    @-}
  (ST g) >>  f = ST (\x -> case g x of {(y, s) -> (runState f) s})    
