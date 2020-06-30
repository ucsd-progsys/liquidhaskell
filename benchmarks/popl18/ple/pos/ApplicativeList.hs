{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ListFunctors where

import Prelude hiding (fmap, id, seq, pure)

import Language.Haskell.Liquid.ProofCombinators

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u


{-@ reflect pure @-}
pure :: a -> L a
pure x = C x N

{-@ reflect seq @-}
seq :: L (a -> b) -> L a -> L b
seq (C f fs) xs
  = append (fmap f xs) (seq fs xs)
seq N xs
  = N

{-@ reflect append @-}
append :: L a -> L a -> L a
append N ys
  = ys
append (C x xs) ys
  = C x (append xs ys)

{-@ reflect fmap @-}
fmap f N        = N
fmap f (C x xs) = C (f x) (fmap f xs)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


{-@ automatic-instances identity @-}

-- | Identity
{-@ identity :: x:L a -> { seq (pure id) x == x } @-}
identity :: L a -> Proof
identity xs
  = fmap_id xs &&& prop_append_neutral xs

-- | Composition

{-@ composition :: x:L (a -> a)
                -> y:L (a -> a)
                -> z:L a
                -> { seq (seq (seq (pure compose) x) y) z == seq x (seq y z) } @-}
composition :: L (a -> a) -> L (a -> a) -> L a -> Proof

composition N ys zs 
  =  seq_nill (pure compose)

composition (C x xs) ys zs 
  =   prop_append_neutral (fmap compose (C x xs))
  &&& prop_append_neutral (fmap compose (C x xs))
  &&& seq_append (fmap (compose x) ys) (seq (fmap compose xs) ys) zs
  &&& seq_fmap x ys zs
  &&& prop_append_neutral (fmap compose xs)
  &&& composition xs ys zs

-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(a -> a) -> x:a
                 -> {  seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  = prop_append_neutral (C (f x) N)

-- | interchange


interchange :: L (a -> a) -> a -> Proof
{-@ interchange :: u:(L (a -> a)) -> y:a
     -> { seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange N y
  = seq_nill (pure (idollar y))

interchange (C x xs) y
   =   prop_append_neutral (fmap (idollar y) (C x xs)) 
   &&& seq_one' (idollar y) xs 
   &&& interchange xs y
   &&& seq_prop xs y 


{-@ seq_prop :: xs:L (a -> a) -> y:a -> {seq xs (C y N) == seq xs (pure y)} @-}
seq_prop :: L (a -> a) -> a -> Proof 
seq_prop _ _ = trivial 


data L a = N | C a (L a)
{-@ data L [llen] a = N | C {x :: a, xs :: L a } @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs


-- | TODO: Cuurently I cannot improve proofs
-- | HERE I duplicate the code...

-- TODO: remove stuff out of HERE

{-@ seq_nill :: fs:L (a -> b) -> {v:Proof | seq fs N == N } @-}
seq_nill :: L (a -> b) -> Proof
seq_nill N
  = trivial 
seq_nill (C x xs)
  = seq_nill xs

{-@ append_fmap :: f:(a -> b) -> xs:L a -> ys: L a
      -> {append (fmap f xs) (fmap f ys) == fmap f (append xs ys) } @-}
append_fmap :: (a -> b) -> L a -> L a -> Proof
append_fmap _ N _         = trivial 
append_fmap f (C _ xs) ys = append_fmap f xs ys  

seq_fmap :: (a -> a) -> L (a -> a) -> L a -> Proof
{-@ seq_fmap :: f: (a -> a) -> fs:L (a -> a) -> xs:L a
         -> { seq (fmap (compose f) fs) xs == fmap f (seq fs xs) }
  @-}
seq_fmap _ N _         = trivial
seq_fmap f (C g gs) xs
  =   seq_fmap f gs xs 
  &&& append_fmap f (fmap g xs) (seq gs xs) 
  &&& map_fusion0 f g xs

{-@ append_distr :: xs:L a -> ys:L a -> zs:L a
      -> {v:Proof | append xs (append ys zs) == append (append xs ys) zs } @-}
append_distr :: L a -> L a -> L a -> Proof
append_distr N _ _ = trivial
append_distr (C _ xs) ys zs = append_distr xs ys zs 


{-@ seq_one' :: f:((a -> b) -> b) -> xs:L (a -> b) -> {fmap f xs == seq (pure f) xs} @-}
seq_one' :: ((a -> b) -> b) -> L (a -> b) -> Proof
seq_one' _ N = trivial
seq_one' f (C _ xs) = seq_one' f xs 

{-@ seq_one :: xs:L (a -> b) -> {v:Proof | fmap compose xs == seq (pure compose) xs} @-}
seq_one :: L (a -> b) -> Proof
seq_one N = trivial
seq_one (C _ xs) = seq_one xs 

{-@ seq_append :: fs1:L (a -> b) -> fs2: L (a -> b) -> xs: L a
      -> { seq (append fs1 fs2) xs == append (seq fs1 xs) (seq fs2 xs) } @-}
seq_append :: L (a -> b) -> L (a -> b) -> L a -> Proof
seq_append N _ _ = trivial 
seq_append (C f1 fs1) fs2 xs 
  =   append_distr (fmap f1 xs) (seq fs1 xs) (seq fs2 xs) 
  &&& seq_append fs1 fs2 xs 

{-@ map_fusion0 :: f:(a -> a) -> g:(a -> a) -> xs:L a
      -> {v:Proof | fmap (compose f g) xs == fmap f (fmap g xs) } @-}
map_fusion0 :: (a -> a) -> (a -> a) -> L a -> Proof
map_fusion0 _ _ N = trivial
map_fusion0 f g (C _ xs) = map_fusion0 f g xs


-- | FunctorList
{-@ fmap_id :: xs:L a -> {v:Proof | fmap id xs == id xs } @-}
fmap_id :: L a -> Proof
fmap_id N
  = trivial
fmap_id (C x xs)
  = fmap_id xs

-- imported from Append
prop_append_neutral :: L a -> Proof
{-@ prop_append_neutral :: xs:L a -> {v:Proof | append xs N == xs }  @-}
prop_append_neutral N
  = trivial 
prop_append_neutral (C x xs)
  = prop_append_neutral xs
