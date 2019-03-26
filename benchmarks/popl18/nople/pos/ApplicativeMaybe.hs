{-@ LIQUID "--reflection"     @-}

module ApplicativeMaybe where

import Prelude hiding (fmap, id, seq, pure)

import Language.Haskell.Liquid.ProofCombinators

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u


{-@ reflect pure @-}
pure :: a -> Maybe a
pure x = Just x

{-@ reflect seq @-}
seq :: Maybe (a -> b) -> Maybe a -> Maybe b
seq (Just f) (Just x) = Just (f x)
seq _         _       = Nothing

{-@ reflect fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f (Just x) = Just (f x)
fmap f Nothing  = Nothing

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


-- | Identity

{-@ identity :: x:Maybe a -> {v:Proof | seq (pure id) x == x } @-}
identity :: Maybe a -> Proof
identity Nothing
  = seq (pure id) Nothing
  === Nothing
  *** QED 

identity (Just x)
  = seq (pure id) (Just x)
  === seq (Just id) (Just x)
  === Just (id x)
  === Just x
  *** QED 


-- | Composition

{-@ composition :: x:Maybe (a -> a)
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> {v:Proof | (seq (seq (seq (pure compose) x) y) z) = seq x (seq y z) } @-}
composition :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
composition Nothing y z
  =   seq (seq (seq (pure compose) Nothing) y) z
  === seq (seq Nothing y) z
  === seq Nothing z
  === Nothing
  === seq Nothing (seq y z)
  *** QED 

composition x Nothing z
  =   seq (seq (seq (pure compose) x) Nothing) z
  === seq Nothing z
  === Nothing
  === seq Nothing z
  === seq x (seq Nothing z)
  *** QED 

composition x y Nothing
  =  seq (seq (seq (pure compose) x) y) Nothing
  === Nothing
  === seq y Nothing
  === seq x (seq y Nothing)
  *** QED 


composition (Just x) (Just y) (Just z)
  =   seq (seq (seq (pure compose) (Just x)) (Just y)) (Just z)
  === seq (seq (seq (Just compose) (Just x)) (Just y)) (Just z)
  === seq (seq (Just (compose x)) (Just y)) (Just z)
  === seq (Just (compose x y)) (Just z)
  === Just (compose x y z)
  === Just (x (y z))
  === Just (x (select_Just_1 (Just (y z))))
  === Just (x (select_Just_1 (seq (Just y) (Just z))))
  === seq (Just x) (seq (Just y) (Just z))
  *** QED 


-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(a -> a) -> x:a
                 -> {v:Proof | seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  = seq (pure f) (pure x)
  === seq (Just f) (Just x)
  === Just (f x)
  === pure (f x)
  *** QED 

-- | interchange

interchange :: Maybe (a -> a) -> a -> Proof
{-@ interchange :: u:(Maybe (a -> a)) -> y:a
     -> {v:Proof | seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange Nothing y
  =  seq Nothing (pure y)
  === Nothing
  === seq (pure (idollar y)) Nothing
  *** QED 

interchange (Just f) y
  = seq (Just f) (pure y)
  === seq (Just f) (Just y)
  === Just (f y)
  === Just (idollar y f)
  === Just ((idollar y) f)
  === seq (Just (idollar y)) (Just f)
  === seq (pure (idollar y)) (Just f)
  *** QED 

-- data Maybe a = Nothing | Just a

{-@ measure select_Just_1 @-}
select_Just_1 :: Maybe a -> a

{-@ select_Just_1 :: xs:{Maybe a | is_Just xs } -> a @-}
select_Just_1 (Just x) = x

{-@ measure is_Just @-}
is_Just :: Maybe a -> Bool
is_Just (Just _) = True
is_Just _        = False
