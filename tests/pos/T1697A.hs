-------------------------------------------------------------------------------------------
-- | Fixed User (WORKING)
-------------------------------------------------------------------------------------------

module T1697A where

data User = U

{-@ measure currentUser :: User @-}

{-@ data TaggedT m a <label :: User -> Bool, clear :: User -> Bool> = TaggedT _ @-}
data TaggedT m a = TaggedT { unTag :: m a }
{-@ data variance TaggedT invariant covariant contravariant covariant @-}

instance Functor m => Functor (TaggedT m) where
  fmap f = TaggedT . fmap f . unTag

instance Applicative m => Applicative (TaggedT m) where
  pure = TaggedT . pure
  f <*> x = TaggedT $ unTag f <*> unTag x

{-@
instance Monad m => Monad (TaggedT m) where
  >>= :: forall < p :: User -> Bool
                , q :: User -> Bool
                , r :: User -> Bool
                , s :: User -> Bool
                , t :: User -> Bool
                , u :: User -> Bool
                , rx :: a -> Bool
                , rf :: a -> b -> Bool
                , ro :: b -> Bool
                >.
    {content :: a<rx> |- b<rf content> <: b<ro>}
    {content :: a<rx> |- b<ro> <: b<rf content>}
    {{v : (User<s>) | True} <: {v : (User<p>) | True}}
    {{v : (User<t>) | True} <: {v : (User<p>) | True}}
    {{v : (User<t>) | True} <: {v : (User<r>) | True}}
    {{v : (User<q>) | True} <: {v : (User<u>) | True}}
    {{v : (User<s>) | True} <: {v : (User<u>) | True}}
    x:TaggedT<p, q> m (a<rx>)
    -> (y:a -> TaggedT<r, s> m (b<rf y>))
    -> TaggedT<t, u> m (b<ro>);

  return :: a -> TaggedT<{\_ -> True}, {\_ -> False}> m a
@-}
instance Monad m => Monad (TaggedT m) where
  x >>= f = TaggedT $ unTag x >>= \y -> unTag (f y)
  
-------------------------------------------------------------------------------------------
-- | Test
-------------------------------------------------------------------------------------------

{-@ assume respondT :: String -> TaggedT<{\_ -> True}, {\v -> v == currentUser}> m () @-}
respondT :: String -> TaggedT m ()
respondT = undefined

{-@ test :: TaggedT<{\_ -> True}, {\v -> v == currentUser}> m () @-}
test :: Monad m => TaggedT m ()
test = return "a" >>= respondT
