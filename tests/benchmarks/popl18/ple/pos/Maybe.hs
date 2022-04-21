{-@ LIQUID "--reflection"     @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module Maybe where


import Prelude hiding (Maybe(..), pure, seq)

data Maybe a = Nothing | Just a
{-@ data Maybe a = Nothing | Just a @-}


{-@ reflect seqm @-}
seqm :: Maybe (a -> b) -> Maybe a -> Maybe b
seqm (Just f) (Just x) = Just (f x)
seqm _         _       = Nothing

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ reflect purem @-}
purem :: a -> Maybe a
purem x = Just x

{-

import Prelude hiding (fmap, id, Maybe(..), seq, pure)

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u







{-@ reflect seq @-}
seq :: Maybe (a -> b) -> Maybe a -> Maybe b
seq (Just f) (Just x) = Just (f x)
seq _         _       = Nothing





-}








