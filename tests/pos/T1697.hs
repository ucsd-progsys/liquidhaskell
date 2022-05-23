{-@ LIQUID "--no-pattern-inline" @-}

module T1697 where

data User = U

{-@ measure currentUser :: User @-}

{-@ data TaggedT user m a <label :: user -> Bool, clear :: user -> Bool> = TaggedT _ @-}
data TaggedT user m a = TaggedT { unTag :: m a }
{-@ data variance TaggedT invariant invariant covariant contravariant covariant @-}

instance Functor m => Functor (TaggedT user m) where
  fmap f = TaggedT . fmap f . unTag

instance Applicative m => Applicative (TaggedT user m) where
  pure = TaggedT . pure
  f <*> x = TaggedT $ unTag f <*> unTag x

{-@
instance Monad m => Monad (TaggedT user m) where
  >>= :: forall < p :: user -> Bool
                , q :: user -> Bool
                , r :: user -> Bool
                , s :: user -> Bool
                , t :: user -> Bool
                , u :: user -> Bool
                , rx :: a -> Bool
                , rf :: a -> b -> Bool
                , ro :: b -> Bool
                >.
    {content :: a<rx> |- b<rf content> <: b<ro>}
    {content :: a<rx> |- b<ro> <: b<rf content>}
    {{v : (user<s>) | True} <: {v : (user<p>) | True}}
    {{v : (user<t>) | True} <: {v : (user<p>) | True}}
    {{v : (user<t>) | True} <: {v : (user<r>) | True}}
    {{v : (user<q>) | True} <: {v : (user<u>) | True}}
    {{v : (user<s>) | True} <: {v : (user<u>) | True}}
    x:TaggedT<p, q> user m (a<rx>)
    -> (y:a -> TaggedT<r, s> user m (b<rf y>))
    -> TaggedT<t, u> user m (b<ro>);

  return :: a -> TaggedT<{\_ -> True}, {\_ -> False}> user m a
@-}
instance Monad m =>  Monad (TaggedT user m) where
  x >>= f = TaggedT $ unTag x >>= \y -> unTag (f y)
  
-------------------------------------------------------------------------------------------
-- | Test
-------------------------------------------------------------------------------------------

{-@ assume respondT :: String -> TaggedT<{\_ -> True}, {\v -> v == currentUser}> User m () @-}
respondT :: String -> TaggedT User m ()
respondT = undefined

{-@ test :: TaggedT<{\_ -> True}, {\v -> v == currentUser}> User m () @-}
test :: Monad m => TaggedT User m ()
test = return "a" >>= respondT
