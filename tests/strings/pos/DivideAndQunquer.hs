{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}


module DivideAndQunquer where 

import Prelude hiding (mconcat, map, split, take, drop)
import Language.Haskell.Liquid.ProofCombinators 


foo ::Int -> List (List a) -> Proof
{- foo :: i:Int -> is:List (List a) -> {pmconcat i is == mconcat is} @-}
foo i is = trivial 


{-@ divideAndQunquer
     :: f:(List i -> List o)
     -> thm:(x1:List i -> x2:List i -> {f (append x1 x2) == append (f x1) (f x2)} )
     -> is:List i 
     -> n:Int 
     -> m:Int 
     -> {f is == mconcat (map f (chunk n is))}
     / [llen is] 
  @-}

--      -> {f is == pmconcat m (map f (chunk n is)) }

divideAndQunquer 
  :: (List i -> List o) 
  -> (List i -> List i -> Proof)
  -> List i -> Int -> Int -> Proof
divideAndQunquer f thm is n m  
  | llen is <= n || n <= 1 
  =   mconcat (map f (chunk n is))
  ==. mconcat (map f (C is N))
  ==. mconcat (f is `C` map f N)
  ==. mconcat (f is `C` N)
  ==. append (f is) (mconcat N)
  ==. append (f is) N
  ==. f is ? appendNeutralRight (f is)
  *** QED 
  | otherwise
  =   mconcat (map f (chunk n is))
  ==. mconcat (map f (C (take n is) (chunk n (drop n is)))) 
  ==. mconcat (f (take n is) `C` map f (chunk n (drop n is)))
  ==. append (f (take n is)) (mconcat (map f (chunk n (drop n is))))
  ==. append (f (take n is)) (f (drop n is))
       ? divideAndQunquer f thm (drop n is) n m 
  ==. f (append (take n is) (drop n is))
       ? thm (take n is) (drop n is)
  ==. f is 
       ? appendTakeDrop n is 
  *** QED 


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


{-@ reflect mconcat @-}
mconcat :: List (List a) -> List a 
mconcat N        = N 
mconcat (C x xs) = append x (mconcat xs)


{-@ reflect pmconcat @-}
pmconcat :: Int -> List (List a) -> List a  
{-@ pmconcat :: i:Int -> is:List (List a) -> List a  /[llen is] @-}

pmconcat i xs
  | i <= 0 
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


appendNeutralRight :: List a -> Proof 
{-@ appendNeutralRight :: xs:List a -> { append xs N == xs } @-}
appendNeutralRight N 
  = append N N ==. N *** QED 
appendNeutralRight (C x xs)
  =   append (C x xs) N 
  ==. C x (append xs N) ? appendNeutralRight xs 
  ==. C x xs 
  *** QED   

{-@ data List [llen] a = N | C {lhead :: a, ltail :: List a} @-}
data List a = N | C a (List a)

llen :: List a -> Int 
{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen N        = 0 
llen (C _ xs) = 1 + llen xs

