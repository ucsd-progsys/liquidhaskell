{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}
{-@ LIQUID "--no-measure-fields"   @-}


module DivideAndQunquer where 

import Prelude hiding (error, map, take, drop)
import Language.Haskell.Liquid.ProofCombinators 

{-@ reflect mapReduce @-}
mapReduce :: Int -> (List a -> b) -> (b -> b -> b) -> List a -> b 
mapReduce n f op N  = f N  
mapReduce n f op is = reduce op (map f (chunk n is)) 

chunk  :: Int -> List a -> List (List a)
map    :: (a -> b) -> List a -> List b
reduce :: (b -> b -> b) -> List b -> b  

{-@ mapReduceTheorem :: n:Int -> f:(List a -> b) -> op:(b -> b -> b) -> is:List a
      -> distributionThm:(is1:List a -> is2:List a -> {op (f is1) (f is2) == f (append is1 is2)} ) -> 
      { f is == mapReduce n f op is } / [llen is] @-}
mapReduceTheorem :: Int -> (List a -> b) -> (b -> b -> b) -> List a -> (List a -> List a -> Proof)  -> Proof 
mapReduceTheorem n f op N _
  =   mapReduce n f op N 
  ==. f N 
  *** QED 

mapReduceTheorem n f op is _ 
  | llen is <= n || n <= 1 
  =   mapReduce n f op is 
  ==. reduce op (map f (chunk n is))
  ==. reduce op (map f (C is N))
  ==. reduce op (f is `C` map f N)
  ==. reduce op (f is `C` N)
  ==. f is
  *** QED 

mapReduceTheorem n f op is distributionThm = undefined   
{- 
  =   mapReduce n f op is 
  ==. reduce op (map f (chunk n is))
  ==. reduce op (map f (C (take n is) (chunk n (drop n is))))
  ==. reduce op (f (take n is) `C` map f (chunk n (drop n is)))
  ==. op (f (take n is)) (reduce op (map f (chunk n (drop n is))))
  ==. op (f (take n is)) (mapReduce n f op (drop n is))
  ==. op (f (take n is)) (f (drop n is))
        ? mapReduceTheorem n f op (drop n is) distributionThm
  ==. f (append (take n is) (drop n is))
        ? distributionThm (take n is) (drop n is)
  ==. f is 
        ? appendTakeDrop n is
  *** QED  
-}
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
{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:List a -> {v:List b | llen v == llen xs } @-}
map _  N       = N
map f (C x xs) = f x `C` map f xs 

{-@ reflect append @-}
append :: List a -> List a -> List a 
append N        ys = ys  
append (C x xs) ys = x `C` (append xs ys)

{-@ reflect reduce @-}
{-@ reduce :: (b -> b -> b) -> is:{List b | 1 <= llen is } -> b @-}  
reduce _  (C x N)  = x 
reduce op (C x xs) = op x (reduce op xs)

{-@ reflect chunk @-}
{-@ chunk :: i:Int -> xs:List a -> {v:List (List a) | (1 <= llen v) &&  (if (i <= 1 || llen xs <= i) then (llen v == 1) else (llen v < llen xs)) } / [llen xs] @-}
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

-- | Helper Theorem 
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

