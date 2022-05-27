{-@ LIQUID "--reflection"     @-}

module ApplicativeList where

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


-- | Identity
{-@ identity :: x:L a -> {v:Proof | seq (pure id) x == x } @-}
identity :: L a -> Proof
identity xs
  =  seq (pure id) xs
  === seq (C id N) xs
  === append (fmap id xs) (seq N xs)
  ==? append (id xs) (seq N xs)      
      ? fmap_id xs
  === append xs (seq N xs)
  === append xs N
  ==? xs                             
      ? prop_append_neutral xs
  *** QED 

-- | Composition

{-@ composition :: x:L (a -> a)
                -> y:L (a -> a)
                -> z:L a
                -> {v:Proof | (seq (seq (seq (pure compose) x) y) z) == seq x (seq y z) } @-}
composition :: L (a -> a) -> L (a -> a) -> L a -> Proof

composition xss@(C x xs) yss@(C y ys) zss@(C z zs)
{- TODO-REBARE: NIKI, please debug if you want, the ple version works fine,
   will be MUCH easier after source-spans are restored.
 -}
  =   seq (seq (seq (pure compose) xss) yss) zss
  === seq (seq (seq (C compose N) xss) yss) zss
  === seq (seq (append (fmap compose xss) (seq N xss)) yss) zss
  === seq (seq (append (fmap compose xss) N) yss) zss
  ==? seq (seq (fmap compose xss) yss) zss 
      ? prop_append_neutral (fmap compose xss)
  === seq (seq (fmap compose (C x xs)) yss) zss
  === seq (seq (C (compose x) (fmap compose xs)) yss) zss
  === seq (append (fmap (compose x) yss) (seq (fmap compose xs) yss)) zss
  === seq (append (fmap (compose x) (C y ys)) (seq (fmap compose xs) yss)) zss
  === seq (append (C (compose x y) (fmap (compose x) ys)) (seq (fmap compose xs) yss)) zss
  === seq (C (compose x y) (append (fmap (compose x) ys) (seq (fmap compose xs) yss))) zss
  === append (fmap (compose x y) zss) (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss)
  === append (fmap (compose x y) (C z zs)) (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss)
  === append (C (compose x y z) (fmap (compose x y) zs)) (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss)
  === C (compose x y z) (append (fmap (compose x y) zs) (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss))
  === C (x (y z))       (append (fmap (compose x y) zs) (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss))
  ==? C (x (y z))       (append (fmap x (fmap y zs))    (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss))
      ? map_fusion0 x y zs
  ==? C (x (y z))       (append (fmap x (fmap y zs))    (append (seq (fmap (compose x) ys) zss) (seq (seq (fmap compose xs) yss) zss)))
      ? seq_append (fmap (compose x) ys) (seq (fmap compose xs) yss) zss
  ==? C (x (y z))       (append (fmap x (fmap y zs))    (append (seq (fmap (compose x) ys) zss) (seq (seq (seq (pure compose) xs) yss) zss)))
      ? seq_one xs
  ==? C (x (y z))       (append (fmap x (fmap y zs))    (append (seq (fmap (compose x) ys) zss) (seq xs (seq yss zss))))
      ? composition xs yss zss
  ==? C (x (y z))       (append (append (fmap x (fmap y zs)) (seq (fmap (compose x) ys) zss))   (seq xs (seq yss zss)))
      ? append_distr (fmap x (fmap y zs)) (seq (fmap (compose x) ys) zss) (seq xs (seq yss zss))
  ==? C (x (y z))       (append (append (fmap x (fmap y zs)) (fmap x (seq ys zss)))   (seq xs (seq yss zss)))
      ? seq_fmap x ys zss
  ==? C (x (y z))       (append (append (fmap x (fmap y zs)) (fmap x (seq ys zss)))   (seq xs (seq yss zss)))
      ? append_fmap x (fmap y zs) (seq ys zss)
  === append (C (x (y z)) (fmap x (append (fmap y zs) (seq ys zss)))) (seq xs (seq yss zss))
  === append (fmap x (C (y z) (append (fmap y zs) (seq ys zss)))) (seq xs (seq yss zss))
  === append (fmap x (append (C (y z) (fmap y zs)) (seq ys zss))) (seq xs (seq yss zss))
  === append (fmap x (append (fmap y (C z zs)) (seq ys zss))) (seq xs (seq yss zss))
  === append (fmap x (append (fmap y zss) (seq ys zss))) (seq xs (seq yss zss))
  === append (fmap x (seq (C y ys) zss)) (seq xs (seq yss zss))
  === append (fmap x (seq yss zss)) (seq xs (seq yss zss))
  === seq (C x xs) (seq yss zss)
  === seq xss (seq yss zss)
  *** QED 

composition N yss zss
   = undefined
{- 
   =   seq (seq (seq (pure compose) N) yss) zss  
   === seq (seq (seq (C compose N) N) yss) zss
   === seq (seq (append (fmap compose N) (seq N N)) yss) zss
   === seq (seq (append N (seq N N)) yss) zss
   === seq (seq (seq N N) yss) zss
   === seq (seq N yss) zss
   === seq yss zss
   === seq N (seq yss zss)
   *** QED 
-}

composition xss N zss
   =   seq (seq (seq (pure compose) xss) N) zss
   ==? seq N zss                            
       ? seq_nill (seq (pure compose) xss)
   === N
   === seq N zss
   ==? seq xss (seq N zss)  
       ? (seq_nill xss ==> (seq N zss === N *** QED))
   *** QED 

composition xss yss N
  =   seq (seq (seq (pure compose) xss) yss) N
  ==? N                    
      ? seq_nill (seq (seq (pure compose) xss) yss)
  ==? seq xss N            
      ? seq_nill xss
  ==? seq xss (seq yss N)  
      ? seq_nill yss
  *** QED 

-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(a -> a) -> x:a
                 -> {v:Proof | seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  =  seq (pure f) (pure x)
  === seq (C f N) (C x N)
  === append (fmap f (C x N)) (seq N (C x N))
  === append (C (f x) (fmap f N)) N
  === append (C (f x) N) N
  ==? C (f x) N  
      ? prop_append_neutral (C (f x) N)
  === pure (f x)
  *** QED 

-- | interchange

interchange :: L (a -> a) -> a -> Proof
{-@ interchange :: u:(L (a -> a)) -> y:a
     -> {v:Proof | seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange N y
  = seq N (pure y)
  === N
  ==? seq (pure (idollar y)) N 
      ? seq_nill (pure (idollar y))
  *** QED 

interchange (C x xs) y
  =  seq (C x xs) (pure y)
  === seq (C x xs) (C y N)
  === append (fmap x (C y N)) (seq xs (C y N))
  === append (C (x y) (fmap x N)) (seq xs (C y N))
  === append (C (x y) N) (seq xs (C y N))
  === C (x y) (append N (seq xs (C y N)))
  === C (x y) (seq xs (C y N))
  === C (x y) (seq xs (pure y))
  ==? C (x y) (seq (pure (idollar y)) xs) 
      ? interchange xs y
  ==? C (x y) (fmap (idollar y) xs)       
      ? seq_one' (idollar y) xs
  === C (idollar y x) (fmap (idollar y) xs)
  === fmap (idollar y) (C x xs)
  ==? append (fmap (idollar y) (C x xs)) N  
      ? prop_append_neutral (fmap (idollar y) (C x xs))
  === append (fmap (idollar y) (C x xs)) (seq N (C x xs))
  === seq (C (idollar y) N) (C x xs)
  === seq (pure (idollar y)) (C x xs)
  *** QED 


{-@ data L [llen] @-} 
data L a = N | C a (L a)

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs








{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (C x _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (C _ xs) = xs

-- | TODO: Cuurently I cannot improve proofs
-- | HERE I duplicate the code...

-- TODO: remove stuff out of HERE

{-@ seq_nill :: fs:L (a -> b) -> {v:Proof | seq fs N == N } @-}
seq_nill :: L (a -> b) -> Proof
seq_nill N
  =   seq N N 
  === N
  *** QED 

seq_nill (C x xs)
  =   seq (C x xs) N
  === append (fmap x N) (seq xs N)
  ==? append N N 
      ? seq_nill xs
  === N
  *** QED 

{-@ append_fmap :: f:(a -> b) -> xs:L a -> ys: L a
   -> {v:Proof | append (fmap f xs) (fmap f ys) == fmap f (append xs ys) } @-}
append_fmap :: (a -> b) -> L a -> L a -> Proof
append_fmap = undefined


seq_fmap :: (a -> a) -> L (a -> a) -> L a -> Proof
{-@ seq_fmap :: f: (a -> a) -> fs:L (a -> a) -> xs:L a
         -> {v:Proof | seq (fmap (compose f) fs) xs == fmap f (seq fs xs) }
  @-}
seq_fmap = undefined

{-@ append_distr :: xs:L a -> ys:L a -> zs:L a
   -> {v:Proof | append xs (append ys zs) == append (append xs ys) zs } @-}
append_distr :: L a -> L a -> L a -> Proof
append_distr = undefined


{-@ seq_one' :: f:((a -> b) -> b) -> xs:L (a -> b) -> {v:Proof | fmap f xs == seq (pure f) xs} @-}
seq_one' :: ((a -> b) -> b) -> L (a -> b) -> Proof
seq_one' = undefined

{-@ seq_one :: xs:L (a -> b) -> {v:Proof | fmap compose xs == seq (pure compose) xs} @-}
seq_one :: L (a -> b) -> Proof
seq_one = undefined

{-@ seq_append :: fs1:L (a -> b) -> fs2: L (a -> b) -> xs: L a
   -> {v:Proof | seq (append fs1 fs2) xs == append (seq fs1 xs) (seq fs2 xs) } @-}
seq_append :: L (a -> b) -> L (a -> b) -> L a -> Proof
seq_append = undefined

{-@ map_fusion0 :: f:(a -> a) -> g:(a -> a) -> xs:L a
    -> {v:Proof | fmap (compose f g) xs == fmap f (fmap g xs) } @-}
map_fusion0 :: (a -> a) -> (a -> a) -> L a -> Proof
map_fusion0 = undefined

-- | FunctorList
{-@ fmap_id :: xs:L a -> {v:Proof | fmap id xs == id xs } @-}
fmap_id :: L a -> Proof
fmap_id N
  =   fmap id N 
  === N
  === id N
  *** QED 

fmap_id (C x xs)
  =   fmap id (C x xs) 
  === C (id x) (fmap id xs)
  === C x (fmap id xs)
  ==? C x (id xs)            
      ? fmap_id xs
  === C x xs
  === id (C x xs)
  *** QED 

-- imported from Append
prop_append_neutral :: L a -> Proof
{-@ prop_append_neutral :: xs:L a -> {v:Proof | append xs N == xs }  @-}
prop_append_neutral N
  =   append N N 
  === N 
  *** QED 

prop_append_neutral (C x xs)
  =   append (C x xs) N 
  === C x (append xs N)
  ==? C x xs             
      ? prop_append_neutral xs
  *** QED


-- | Proof combinators (are Proofean combinators)

{-@ measure proofBool :: Proof -> Bool @-}

{-@ (==>) :: p:Proof
          -> q:Proof
          -> {v:Proof |
          (((proofBool p)) && (proofBool p => (proofBool q)))
          =>
          (((proofBool p) && (proofBool q)))
          } @-}
(==>) :: Proof -> Proof -> Proof
p ==> q = ()

