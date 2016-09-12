-- | Proof of equivalence of MapReduce 
-- | mapReduce n op f is == f is 

-- | Niki Vazou Sep 2016 



{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}


module MapRecude where 

import Prelude hiding (mconcat, map, split, take, drop, sum)
import Language.Haskell.Liquid.ProofCombinators 

-------------------------------------------------------------------------------
------------  Map Reduce Definition  ------------------------------------------
-------------------------------------------------------------------------------


{-@ axiomatize mapReduce @-}
mapReduce :: Int -> (List a -> b) -> (b -> b -> b) -> List a -> b 
mapReduce n f op is = reduce op (f N) (map f (chunk n is))

{-@ axiomatize reduce @-}
reduce :: (a -> a -> a) -> a -> List a -> a 
reduce op b N        = b 
reduce op b (C x xs) = op x (reduce op b xs) 

chunk :: Int -> List a -> List (List a)


-------------------------------------------------------------------------------
------------  Application: List sum  ------------------------------------------
-------------------------------------------------------------------------------

sum  :: List Int -> Int 
plus :: Int -> Int -> Int 

{-@ axiomatize msum @-}
msum :: Int -> List Int -> Int 
msum n is = mapReduce n sum plus is 


mapReduceSum :: Int -> List Int -> Proof 
{-@ mapReduceSum :: n:Int -> is:List Int -> { sum is == mapReduce n sum plus is} @-}
mapReduceSum n is 
  =   msum n is 
  ==. mapReduce n sum plus is 
  ==. sum is  ? mapReduceTheorem n sum plus sumLeftId sumDistributes is 
  *** QED 

-------------------------------------------------------------------------------
------------  Main MapReduce Theorem ------------------------------------------
-------------------------------------------------------------------------------


mapReduceTheorem :: Int -> (List a -> b) -> (b -> b -> b) -> (List a -> Proof) -> (List a -> List a -> Proof) -> List a -> Proof 
{-@ mapReduceTheorem :: n:Int -> f:(List a -> b) -> op:(b -> b -> b)
     -> left_id:(xs:List a -> {op (f xs) (f N) == f xs } ) 
     -> distributionTheorem:(xs:List a -> ys:List a -> {f (append xs ys) == op (f xs) (f ys)} )
     -> is:List a ->
     { mapReduce n f op is == f is }
     / [llen is]
  @-}
mapReduceTheorem n f op left_id _ N 
  =   mapReduce n f op N 
  ==. reduce op (f N) (map f (chunk n N))
  ==. reduce op (f N) (map f (C N N))
  ==. reduce op (f N) (f N `C` map f N )
  ==. reduce op (f N) (f N `C` N)
  ==. op (f N) (reduce op (f N) N)
  ==. op (f N) (f N)
       ? left_id N
  ==. f N 
  *** QED 
mapReduceTheorem n f op left_id _ is@(C x xs)
  | n <= 1 || llen is <= n 
  =   mapReduce n f op is 
  ==. reduce op (f N) (map f (chunk n is))
  ==. reduce op (f N) (map f (C is N))
  ==. reduce op (f N) (f is `C` map f N)
  ==. reduce op (f N) (f is `C` N)
  ==. op (f is) (reduce op (f N) N)
  ==. op (f is) (f N)
  ==. f is  ? left_id is
  *** QED 
mapReduceTheorem n f op left_id distributionTheorem is 
  =   mapReduce n f op is 
  ==. reduce op (f N) (map f (chunk n is)) 
  ==. reduce op (f N) (map f (C (take n is) (chunk n (drop n is)))) 
  ==. reduce op (f N) (C (f (take n is)) (map f (chunk n (drop n is)))) 
  ==. op (f (take n is)) (reduce op (f N) (map f (chunk n (drop n is))))  
  ==. op (f (take n is)) (mapReduce n f op (drop n is)) 
      ? mapReduceTheorem n f op left_id distributionTheorem (drop n is)
  ==. op (f (take n is)) (f (drop n is)) 
  ==. f (append (take n is) (drop n is))
      ? distributionTheorem (take n is) (drop n is)
  ==. f is 
      ? appendTakeDrop n is 
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


{-@ reflect append @-}
append :: List a -> List a -> List a 
append N        ys = ys  
append (C x xs) ys = x `C` (append xs ys)


-------------------------------------------------------------------------------
-----------  Helper Theorems --------------------------------------------------
-------------------------------------------------------------------------------


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



-------------------------------------------------------------------------------
------------  Application: List sum  ------------------------------------------
-------------------------------------------------------------------------------


sumLeftId :: List Int -> Proof 
{-@ sumLeftId :: xs:List Int -> {plus (sum xs) (sum N) == sum xs } @-}
sumLeftId xs 
  =  plus (sum xs) (sum N) ==. sum xs + 0 ==. sum xs *** QED 

{-@ sumDistributes :: xs:List Int -> ys:List Int -> 
      {sum (append xs ys) == plus (sum xs) (sum ys)} @-}
sumDistributes :: List Int -> List Int -> Proof 
sumDistributes N ys 
  =   sum (append N ys)
  ==. sum ys
  ==. plus 0       (sum ys)
  ==. plus (sum N) (sum ys)
  *** QED 
sumDistributes (C x xs) ys  
  =   sum (append (C x xs) ys)
  ==. sum (C x (append xs ys))
  ==. x `plus` (sum (append xs ys))
      ? sumDistributes xs ys
  ==. x `plus` (plus (sum xs) (sum ys))
  ==. x + (sum xs + sum ys)
  ==. ((x + sum xs) + sum ys)
  ==. ((x `plus` sum xs) `plus` sum ys)
  ==. sum (C x xs) `plus` sum ys
  *** QED 


{-@ axiomatize plus @-}
plus x y = x + y 

{-@ axiomatize sum @-}
sum N        = 0 
sum (C x xs) = x `plus` sum xs

