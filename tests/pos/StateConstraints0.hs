module Compose where

import Prelude hiding (Monad(..))

-- | TODO 
-- | 
-- | 1. default methods are currently not supported
-- | ie. if we remove the definition of fail method it fails
-- | as I assume that dictionaries are Non Recursive
-- |
-- | 2. check what happens if we import the instance (it should work)  

data ST s a = ST {runState :: s -> (a,s)}

{-@ data ST s a <p :: s -> Bool, q :: s -> s -> Bool, r :: s -> a -> Bool> 
  = ST (runState :: x:s<p> -> (a<r x>, s<q x>)) @-}

{-@ runState :: forall <p :: s -> Bool, q :: s -> s -> Bool, r :: s -> a -> Bool>. ST <p, q, r> s a -> x:s<p> -> (a<r x>, s<q x>) @-}


class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b
  (>>)   :: m a -> m b -> m b


instance Monad (ST s) where
  {-@ instance Monad ST s where
    return :: forall s a <p :: s -> Bool >. x:a -> ST <p, {\s v -> v == s}, {\s v -> x == v}> s a;
    >>= :: forall s a b  < pref :: s -> Bool, postf :: s -> s -> Bool
              , pre  :: s -> Bool, postg :: s -> s -> Bool
              , post :: s -> s -> Bool
              , rg   :: s -> a -> Bool
              , rf   :: s -> b -> Bool
              , r    :: s -> b -> Bool
              , pref0 :: a -> Bool 
              >. 
       {x::s<pre> |- a<rg x> <: a<pref0>}      
       {x::s<pre>, y::s<postg x> |- b<rf y> <: b<r x>}
       {xx::s<pre>, w::s<postg xx> |- s<postf w> <: s<post xx>}
       {ww::s<pre> |- s<postg ww> <: s<pref>}
       (ST <pre, postg, rg> s a)
    -> (a<pref0> -> ST <pref, postf, rf> s b)
    -> (ST <pre, post, r> s b) ;
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
  return x     = ST $ \s -> (x, s)
  (ST g) >>= f = ST (\x -> case g x of {(y, s) -> (runState (f y)) s})    
  (ST g) >>  f = ST (\x -> case g x of {(y, s) -> (runState f) s})    

{-@ incr :: ST <{\x -> true}, {\x v -> v = x + 1}, {\x v -> v = x}>  Int Int @-}
incr :: ST Int Int
incr = ST $ \x ->  (x, x + 1)

{-@ foo :: ST <{\x -> true}, {\x v -> true}, {\x v -> v = 0}>  Bool Int @-}
foo :: ST Bool Int
foo = return 0

{-@ incr2 :: ST <{\x -> true}, {\x v -> v = x + 2}, {\x v -> v = x + 1}>  Int Int @-}
incr2 :: ST Int Int
incr2 = incr >> incr

{-@ incr3 :: ST <{\x -> true}, {\x v -> v = x + 3}, {\x v -> v = x + 2}>  Int Int @-}
incr3 :: ST Int Int
incr3 
  = incr >> incr >> incr

run :: (Int, Int)
{-@ run :: ({v:Int |  v = 1}, {v:Int |  v = 2}) @-}
run = (runState incr2) 0






















