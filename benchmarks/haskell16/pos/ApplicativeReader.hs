{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ApplicativeReader where

import Prelude hiding (fmap, id, seq, pure)

import Proves
import Helper (lambda_expand)

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u

{-@ data Reader r a = Reader { runIdentity :: r -> a } @-}
data Reader r a     = Reader { runIdentity :: r -> a }

{-@ measure fromReader @-}
fromReader :: Reader r a -> (r -> a)
fromReader (Reader f) = f 


{-@ axiomatize pure @-}
pure :: a -> Reader r a
pure x = Reader (\r -> x)

{-@ axiomatize seq @-}
seq :: Reader r (a -> b) -> Reader r a -> Reader r b
seq (Reader f) (Reader x) = Reader (\r -> (f r) (x r))

{-@ axiomatize idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ axiomatize id @-}
id :: a -> a
id x = x

-- | Identity

{-@ identity :: x:Reader r a 
  -> { seq (pure id) x == x } @-}
identity :: Arg r => Reader r a -> Proof
identity (Reader r)
  =   seq (pure id) (Reader r)
  ==! seq (Reader (\w -> id)) (Reader r)
  ==! Reader (\q -> ((\w -> id) (q)) (r q))   
  ==! Reader (\q -> (id) (r q))            ? id_helper1 r
  ==! Reader (\q -> r q)                   ? id_helper2 r 
  ==! Reader r                             ? lambda_expand r 
  *** QED 


-- NV: The following are the required helper functions as 
-- we have no other way to prove equalities burried in lambdas. 
-- This should be simplified

 

id_helper2 :: Arg r => (r -> a) -> Proof 
{-@ id_helper2 :: r:(r -> a) 
  -> { (\q:r -> r q) == (\q:r -> (id) (r q)) } @-}
id_helper2 r 
  = ((\q -> r q) =*=! (\q -> (id) (r q))) (id_helper2_body r)
  *** QED 


id_helper2_body :: Arg r => (r -> a) -> r ->  Proof 
{-@ id_helper2_body :: r:(r -> a) -> q:r
  -> { (r q == (id) (r q)) 
    && (( (\q:r -> r q) (q)) == r q)
    && (((\q:r -> (id) (r q)) (q)) == id (r q))
     } @-}
id_helper2_body r q
  = r q ==! id (r q) *** QED 


id_helper1 :: Arg r => (r -> a) -> Proof 
{-@ id_helper1 :: r:(r -> a) 
  -> { (\q:r -> (((\w:r -> id) (q)) (r q))) == (\q:r -> (id) (r q)) } @-}
id_helper1 r 
  = ((\q -> (((\w -> id) q) (r q))) =*=! (\q -> id (r q))) (id_helper1_body r)
  *** QED 


{-@ id_helper1_body :: r:(r -> a) -> q:r
  -> {(((\w:r -> id) (q)) (r q)) == (id) (r q) } @-}
id_helper1_body :: Arg r => (r -> a) -> r -> Proof 
id_helper1_body r q 
  =   ((\w -> id) q) (r q)
  ==! id (r q)
  *** QED   



-- | Composition

{- composition :: x:Reader r (a -> a)
                -> y:Reader r (a -> a)
                -> z:Reader r a
                -> { (seq (seq (seq (pure compose) x) y) z) == seq x (seq y z) } @-}
composition :: Reader r (a -> a) -> Reader r (a -> a) -> Reader r a -> Proof
composition (Reader x) (Reader y) (Reader z)
  =   seq (seq (seq (pure compose) (Reader x)) (Reader y)) (Reader z) 
  ==! seq (seq (seq (Reader (\r1 -> compose)) (Reader x)) (Reader y)) (Reader z)
  ==! seq (seq (Reader (\r2 -> ((\r1 -> compose) r2) (x r2))) (Reader y)) (Reader z)
  ==! seq (seq (Reader (\r2 -> compose (x r2))) (Reader y)) (Reader z)
  ==! seq (Reader (\r3 -> ((\r2 -> compose (x r2)) r3) (y r3))) (Reader z)
  ==! seq (Reader (\r3 -> (compose (x r3)) (y r3))) (Reader z)
  ==! Reader (\r4 -> ((\r3 -> (compose (x r3)) (y r3)) r4) (z r4)) 
  ==! Reader (\r4 -> (compose (x r4) (y r4)) (z r4)) 
  ==! Reader (\r4 -> (x r4) ((y r4) (z r4)))
  ==! Reader (\r4 -> (x r4) ((\r5 -> (y r5) (z r5)) r4))
  ==! seq (Reader x) (Reader (\r5 -> (y r5) (z r5)))
  ==! seq (Reader x) (seq (Reader y) (Reader z))
  *** QED 


-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(a -> a) -> x:a
                 -> { seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  =   seq (pure f) (pure x)
  ==! seq (Reader (\r2 -> f)) (Reader (\r2 -> x))
  ==! Reader (\r -> ((\r2 -> f) r ) ((\r2 -> x) r))
  ==! Reader (\r -> f x)
  ==! pure (f x)
  *** QED 

-- | interchange

interchange :: Arg r => Reader r (a -> a) -> a -> Proof
{-@ interchange :: u:(Reader r (a -> a)) -> y:a
     -> { seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange (Reader f) x
  =   seq (Reader f) (pure x)
  ==! seq (Reader f) (Reader (\r -> x))
  ==! Reader (\r' -> (f r') ((\r -> x) r'))
  ==! Reader (\r' -> (f r') x)                           ? interchange_helper_0 f x -- this is not required
  ==! Reader (\r' -> (idollar x) (f r'))                 ? interchange_helper_1 f x 
  ==! Reader (\r' -> ((\r'' -> (idollar x)) r') (f r'))  ? interchange_helper_2 f x 
  ==! seq (Reader (\r'' ->  (idollar x))) (Reader f)
  ==! seq (pure (idollar x)) (Reader f)
  *** QED 


{-@ interchange_helper_0
  :: f:(r -> (a -> a)) -> x:a 
  -> {(\r':r -> (f r') (x)) == (\r':r -> (f r') ((\r:r -> x) (r')) )}
  @-} 
interchange_helper_0 :: Arg r => (r -> (a -> a)) -> a -> Proof 
interchange_helper_0 f x
  = (((\r -> (f r) x) =*=! (\r -> (f r) ((\r' -> x) r))) 
    (\_ -> simpleProof)) *** QED  


{-@ interchange_helper_1 
  :: f:(r -> (a -> a)) -> x:a 
  -> {(\r':r -> (f r') (x)) == (\r':r -> (idollar x) (f r'))}
  @-} 
interchange_helper_1 :: Arg r => (r -> (a -> a)) -> a -> Proof 
interchange_helper_1 f x 
  =  (((\r -> (f r) x) =*=! (\r -> (idollar x) (f r))) (interchange_helper_1_body f x)) *** QED 

{-@ interchange_helper_1_body 
  :: f:(r -> (a -> a)) -> x:a -> r':r
  -> {((f r') (x) == (idollar x) (f r'))
     && ((\r':r -> (f r') (x)) (r')  ==  (f r') (x))
     && ((\r':r -> (idollar x) (f r')) (r') == (idollar x) (f r'))
     }
  @-} 
interchange_helper_1_body :: Arg r => (r -> (a -> a)) -> a -> r -> Proof 
interchange_helper_1_body f x r 
  = f r x ==! (idollar x) (f r) *** QED 


{-@ interchange_helper_2 
  :: f:(r -> (a -> a)) -> x:a 
  -> {(\r':r -> ((\r'':r -> (idollar x)) (r')) (f r')) == (\r':r -> (idollar x) (f r'))}
  @-} 
interchange_helper_2 :: Arg r => (r -> (a -> a)) -> a -> Proof 
interchange_helper_2 f x 
  =    (((\r' -> ((\r'' -> (idollar x)) (r')) (f r')) ) 
  =*=! (\r' -> (idollar x) (f r'))
       ) (interchange_helper_2_body f x) *** QED 

{-@ interchange_helper_2_body 
  :: f:(r -> (a -> a)) -> x:a -> r':r
  -> {(\r':r -> ((\r'':r -> (idollar x)) (r')) (f r')) == (\r':r -> (idollar x) (f r'))}
  @-} 
interchange_helper_2_body :: Arg r => (r -> (a -> a)) -> a -> r -> Proof 
interchange_helper_2_body f x r'
  =    ((\r'' -> (idollar x)) (r')) (f r')
  ==!  (idollar x) (f r')
  *** QED 





{-@ qual :: f:(r -> a) -> {v:Reader r a | v == Reader f} @-}
qual :: (r -> a) -> Reader r a 
qual = Reader 
 