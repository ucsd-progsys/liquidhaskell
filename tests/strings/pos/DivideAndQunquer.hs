{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}


module DivideAndQunquer where 

import Prelude hiding (mconcat, map, split, take, drop)
import Language.Haskell.Liquid.ProofCombinators 


{-@ divideAndQunquer
     :: f:(List i -> List o)
     -> thm:(x1:List i -> x2:List i -> {f (append x1 x2) == append (f x1) (f x2)} )
     -> is:List i 
     -> n:Int 
     -> m:Int 
     -> {f is == pmconcat m (map f (chunk n is))}
     / [llen is] 
  @-}

divideAndQunquer 
  :: (List i -> List o) 
  -> (List i -> List i -> Proof)
  -> List i -> Int -> Int -> Proof
divideAndQunquer f thm is n m  
  =   pmconcat m (map f (chunk n is))
  ==. mconcat (map f (chunk n is))
       ? pmconcatEquivalence m (map f (chunk n is))
  ==. f is 
       ? distributeInput f thm is n 
  *** QED 

{-@ distributeInput
     :: f:(List i -> List o)
     -> thm:(x1:List i -> x2:List i -> {f (append x1 x2) == append (f x1) (f x2)} )
     -> is:List i 
     -> n:Int 
     -> {f is == mconcat (map f (chunk n is))}
     / [llen is] 
  @-}

distributeInput 
  :: (List i -> List o) 
  -> (List i -> List i -> Proof)
  -> List i -> Int -> Proof
distributeInput f thm is n  
  | llen is <= n || n <= 1
  =   mconcat (map f (chunk n is))
  ==. mconcat (map f (C is N))
  ==. mconcat (f is `C` map f N)
  ==. mconcat (f is `C` N)
  ==. append (f is) (mconcat N)
  ==. append (f is) N
  ==. f is ? appendRightIdentity (f is)
  *** QED 
  | otherwise
  =   mconcat (map f (chunk n is))
  ==. mconcat (map f (C (take n is) (chunk n (drop n is)))) 
  ==. mconcat (f (take n is) `C` map f (chunk n (drop n is)))
  ==. append (f (take n is)) (mconcat (map f (chunk n (drop n is))))
  ==. append (f (take n is)) (f (drop n is))
       ? distributeInput f thm (drop n is) n  
  ==. f (append (take n is) (drop n is))
       ? thm (take n is) (drop n is)
  ==. f is 
       ? appendTakeDrop n is 
  *** QED 

pmconcatEquivalence ::Int -> List (List a) -> Proof
{-@ pmconcatEquivalence :: i:Int -> is:List (List a) 
    -> {pmconcat i is == mconcat is} 
    / [llen is] @-}
pmconcatEquivalence i is 
  | i <= 1
  = pmconcat i is ==. mconcat is *** QED 
pmconcatEquivalence i N 
  =   pmconcat i N 
  ==. N 
  ==. mconcat N 
  *** QED 
pmconcatEquivalence i (C x N) 
  =   pmconcat i (C x N)
  ==. x 
  ==. append x N
       ? appendRightIdentity x  
  ==. mconcat (C x (mconcat N)) 
  ==. mconcat (C x N) 
  *** QED 
pmconcatEquivalence i xs 
  | llen xs <= i 
  =   pmconcat i xs 
  ==. pmconcat i (map mconcat (chunk i xs))
  ==. pmconcat i (map mconcat (C xs N))
  ==. pmconcat i (mconcat xs `C`  map mconcat N)
  ==. pmconcat i (mconcat xs `C`  N)
  ==. mconcat xs
  *** QED 
pmconcatEquivalence i xs
  =   pmconcat i xs 
  ==. pmconcat i (map mconcat (chunk i xs))
  ==. mconcat (map mconcat (chunk i xs))
       ? pmconcatEquivalence i (map mconcat (chunk i xs))
  ==. mconcat xs
       ? mconcatAssoc i xs
  *** QED 

-------------------------------------------------------------------------------
-----------  List Definition --------------------------------------------------
-------------------------------------------------------------------------------


{-@ data List [llen] a = N | C {lhead :: a, ltail :: List a} @-}
data List a = N | C a (List a)

llen :: List a -> Int 
{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen N        = 0 
llen (C _ xs) = 1 + llen xs

-------------------------------------------------------------------------------
-----------  List Manipulation ------------------------------------------------
-------------------------------------------------------------------------------

-- Distribution 

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:List a -> {v:List b | llen v == llen xs } @-}
map :: (a -> b) -> List a -> List b
map _  N       = N
map f (C x xs) = f x `C` map f xs 

{-@ reflect chunk @-}
{-@ chunk :: i:Int -> xs:List a -> {v:List (List a) | if (i <= 1 || llen xs <= i) then (llen v == 1) else (llen v < llen xs) } / [llen xs] @-}
chunk :: Int -> List a -> List (List a)
chunk i xs 
  | i <= 1 
  = C xs N 
  | llen xs <= i 
  = C xs N 
  | otherwise
  = C (take i xs) (chunk i (drop i xs))

{-@ reflect drop @-}
{-@ drop :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == llen xs - i } @-} 
drop :: Int -> List a -> List a 
drop i N = N 
drop i (C x xs)
  | i == 0 
  = C x xs  
  | otherwise 
  = drop (i-1) xs 

{-@ reflect take @-}
{-@ take :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == i} @-} 
take :: Int -> List a -> List a 
take i N = N 
take i (C x xs)
  | i == 0 
  = N  
  | otherwise 
  = C x (take (i-1) xs)

-- Monoid

{-@ reflect mconcat @-}
mconcat :: List (List a) -> List a 
mconcat N        = N 
mconcat (C x xs) = append x (mconcat xs)


{-@ reflect pmconcat @-}
pmconcat :: Int -> List (List a) -> List a  
{-@ pmconcat :: i:Int -> is:List (List a) -> List a  /[llen is] @-}

pmconcat i xs
  | i <= 1 
  = mconcat xs 
pmconcat i N   
  = N 
pmconcat i (C x N) 
  = x
pmconcat i xs 
  = pmconcat i (map mconcat (chunk i xs))

{-@ reflect append @-}
append :: List a -> List a -> List a 
append N        ys = ys  
append (C x xs) ys = x `C` (append xs ys)


-------------------------------------------------------------------------------
-----------  Helper Theorems --------------------------------------------------
-------------------------------------------------------------------------------

-- List is a Monoid 

appendRightIdentity :: List a -> Proof 
{-@ appendRightIdentity :: xs:List a -> { append xs N == xs } @-}

appendRightIdentity N 
  = append N N ==. N *** QED 
appendRightIdentity (C x xs)
  =   append (C x xs) N 
  ==. C x (append xs N) ? appendRightIdentity xs 
  ==. C x xs 
  *** QED   

appendAssoc :: List a -> List a -> List a -> Proof 
{-@ appendAssoc :: x:List a -> y:List a -> z:List a 
  -> {append (append x y) z == append x (append y z)} @-}
appendAssoc N y z 
  =   append (append N y) z 
  ==. append N z 
  ==. N
  ==. append N (append y z)
  *** QED 
appendAssoc (C x xs) y z 
  =   append (append (C x xs) y) z 
  ==. append (x `C` (append xs y)) z 
  ==. x `C` (append (append xs y) z)
  ==. x `C` (append xs (append y z))
       ? appendAssoc xs y z
  ==. append (C x xs) (append y z)
  *** QED   


-- | Monoid implications 

mconcatAssocOne :: Int -> List (List a) -> Proof 
{-@ mconcatAssocOne :: i:Nat -> xs:{List (List a) | i <= llen xs} 
     -> {mconcat xs == append (mconcat (take i xs)) (mconcat (drop i xs))}
     /[i]
  @-} 
mconcatAssocOne i N 
  =   append (mconcat (take i N)) (mconcat (drop i N)) 
  ==. append (mconcat N) (mconcat N)
  ==. append N N 
      --  ? leftIdentity N 
  ==. N 
  ==. mconcat N 
  *** QED 
mconcatAssocOne i (C x xs)
  | i == 0
  =   append (mconcat (take i (C x xs))) (mconcat (drop i (C x xs))) 
  ==. append (mconcat N) (mconcat (C x xs))
  ==. append N (mconcat (C x xs))
  ==. mconcat (C x xs)
      -- ? leftIdentity (C x xs)
  *** QED 
  | otherwise    
  =   append (mconcat (take i (C x xs))) (mconcat (drop i (C x xs))) 
  ==. append (mconcat (C x (take (i-1) xs))) (mconcat (drop (i-1) xs))
  ==. append (append x (mconcat (take (i-1) xs))) (mconcat (drop (i-1) xs))
       ? appendAssoc x (mconcat (take (i-1) xs)) (mconcat (drop (i-1) xs))
  ==. append x (append (mconcat (take (i-1) xs)) (mconcat (drop (i-1) xs)))
       ? mconcatAssocOne (i-1) xs
  ==. append x (mconcat xs)
  ==. mconcat (C x xs)
  *** QED 

-- Generalization to chunking  

mconcatAssoc :: Int -> List (List a) -> Proof 
{-@ mconcatAssoc :: 
    i:Int -> xs:List (List a) 
  -> { mconcat xs == mconcat (map mconcat (chunk i xs))}
  /  [llen xs] @-}
mconcatAssoc i xs 
  | i <= 1 || llen xs <= i
  =   mconcat (map mconcat (chunk i xs))
  ==. mconcat (map mconcat (C xs N))
  ==. mconcat (mconcat xs `C` map mconcat N)
  ==. mconcat (mconcat xs `C` N)
  ==. append (mconcat xs) (mconcat N)
  ==. append (mconcat xs) N
  ==. mconcat xs 
       ? appendRightIdentity (mconcat xs)
  *** QED  
   | otherwise
   =   mconcat (map mconcat (chunk i xs))
   ==. mconcat (map mconcat (take i xs `C` chunk i (drop i xs)))
   ==. mconcat (mconcat (take i xs) `C` map mconcat (chunk i (drop i xs)))
   ==. append (mconcat (take i xs)) (mconcat (map mconcat (chunk i (drop i xs))))
   ==. append (mconcat (take i xs)) (mconcat (drop i xs))
        ? mconcatAssoc i (drop i xs)
   ==. mconcat xs 
        ? mconcatAssocOne i xs 
   *** QED 



-- | For input Distribution 
{-@ appendTakeDrop :: i:Nat -> xs:{List a | i <= llen xs} 
  -> {xs == append (take i xs) (drop i xs) }  @-}

appendTakeDrop :: Int -> List a -> Proof 
appendTakeDrop i N 
  =   append (take i N) (drop i N)
  ==. append N N 
  ==. N 
  *** QED 
appendTakeDrop i (C x xs)
  | i == 0 
  =   append (take 0 (C x xs)) (drop 0 (C x xs))
  ==. append N (C x xs)
  ==. C x xs 
  *** QED 
  | otherwise
  =   append (take i (C x xs)) (drop i (C x xs))
  ==. append (C x (take (i-1) xs)) (drop (i-1) xs)
  ==. C x (append (take (i-1) xs) (drop (i-1) xs))
  ==. C x xs ? appendTakeDrop (i-1) xs 
  *** QED 

