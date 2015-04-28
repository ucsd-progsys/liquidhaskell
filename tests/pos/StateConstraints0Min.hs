module Compose where

import Control.Applicative

-- | TODO 
-- | 
-- | 1. default methods are currently not supported
-- | ie. if we remove the definition of fail method it fails
-- | as I assume that dictionaries are Non Recursive
-- |
-- | 2. check what happens if we import the instance (it should work)  

data ST s a = ST {runState :: s -> (a,s)}

{-@ data ST s a <p :: s -> Prop, q :: s -> s -> Prop, r :: s -> a -> Prop> 
  = ST (runState :: x:s<p> -> (a<r x>, s<q x>)) @-}

{-@ runState :: forall <p :: s -> Prop, q :: s -> s -> Prop, r :: s -> a -> Prop>. ST <p, q, r> s a -> x:s<p> -> (a<r x>, s<q x>) @-}


instance Functor (ST s) where
instance Applicative (ST s) where


instance Monad (ST s) where
  {-@ instance Monad ST s where
    >>  :: forall s a b  < pref :: s -> Prop, postf :: s -> s -> Prop
              , pre  :: s -> Prop, postg :: s -> s -> Prop
              , post :: s -> s -> Prop
              , rg   :: s -> a -> Prop
              , rf   :: s -> b -> Prop
              , r    :: s -> b -> Prop
              >. 
       {x::s<pre>, y::s<postg x> |- b<rf y> <: b<r x>}
       {xx::s<pre>, w::s<postg xx> |- s<postf w> <: s<post xx>}
       {ww::s<pre> |- s<postg ww> <: s<pref>}
       (ST <pre, postg, rg> s a)
    -> (ST <pref, postf, rf> s b)
    -> (ST <pre, post, r> s b)
    @-}
  (ST g) >>  f = ST (\x -> case g x of {(y, s) -> (runState f) s})    

