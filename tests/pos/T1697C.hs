-------------------------------------------------------------------------------------------
-- | Polymorphic user but defining bind and return as normal functions (WORKING)
-------------------------------------------------------------------------------------------

module T1697C where

data User = U

{-@ measure currentUser :: User @-}

{-@ data TaggedT user m a <label :: user -> Bool, clear :: user -> Bool> = TaggedT _ @-}
data TaggedT user m a = TaggedT { unTag :: m a }
{-@ data variance TaggedT invariant invariant covariant contravariant covariant @-}

{-@
assume bindT :: forall < p :: user -> Bool
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
    -> TaggedT<t, u> user m (b<ro>)
@-}
bindT :: Monad m => TaggedT user m a -> (a -> TaggedT user m b) -> TaggedT user m b
bindT x f = TaggedT $ unTag x >>= \y -> unTag (f y)

{-@ assume returnT :: a -> TaggedT<{\_ -> True}, {\_ -> False}> user m a @-}
returnT :: Monad m => a -> TaggedT user m a
returnT x = TaggedT (return x)

-------------------------------------------------------------------------------------------
-- | Test
-------------------------------------------------------------------------------------------

{-@ assume respondT :: String -> TaggedT<{\_ -> True}, {\v -> v == currentUser}> User m () @-}
respondT :: String -> TaggedT User m ()
respondT = undefined

{-@ test :: TaggedT<{\_ -> True}, {\v -> v == currentUser}> User m () @-}
test :: Monad m => TaggedT User m ()
test = returnT "a" `bindT` respondT
