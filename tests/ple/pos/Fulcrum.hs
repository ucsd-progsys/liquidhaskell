-- TAG: localbinds (xorgs)

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}

{-@ infixr ++              @-}

module Fulcrum where

import Prelude hiding ((++), unzip, take, drop, abs, sum, minimum, min)
import Language.Haskell.Liquid.ProofCombinators 

fv       :: [Int] -> Int -> Int 
fulcrum  :: [Int] -> (Int, Int -> ())
fulcrums :: [Int] -> IMap Int 
fv'      :: [Int] -> Int -> Int -> Int -> Int 

--------------------------------------------------------------------------------
-- | Spec: Fulcrum Value
--------------------------------------------------------------------------------

{-@ reflect fv @-}
{-@ fv :: [Int] -> Nat -> Int @-}
fv xs i = abs (sum (take i xs) - sum (drop i xs))    

{-@ reflect abs @-}
abs :: Int -> Int 
abs n | 0 <= n    = n 
      | otherwise = 0 - n

--------------------------------------------------------------------------------
-- | Impl: Computing Fulcrum Values of a List 
--------------------------------------------------------------------------------

{-@ type ListNE a  = {v:[a] | len v > 0 } @-}      -- Non-empty Lists

{-@ fulcrum :: xs:(ListNE Int) -> (i :: Int, j:Int -> {v:() | (btwn 0 j (len xs)) => fv xs i <= fv xs j}) @-} 
fulcrum xs = argMin (fv xs) (fulcrums xs)

{-@ type FvMap Xs N = {m: GMap Int (fv Xs) | size m = N} @-}

{-@ fulcrums :: xorgs:ListNE Int -> FvMap xorgs (len xorgs) @-}
fulcrums xorgs          = go 0 0 xorgs Emp 
  where 
    total               = sum xorgs
    {-@ go :: i:_ -> {pre:_ | pre == sum (take i xorgs)} -> ys:{ys == drop i xorgs} 
           -> FvMap xorgs i 
           -> FvMap {xorgs} {i + len ys} / [len ys] 
      @-} 
    go _ _   [] m = m 
    go i pre ys m = go (i + 1) pre' ys' m' 
      where
        m'        = Bind i fvi m
        fvi       = fv' xorgs total i pre
        ys'       = tail ys         `withProof` thmDrop    xorgs i ys
        pre'      = (pre + head ys) `withProof` thmSumTake xorgs i ys

{-@ fv' :: xs:_ -> total:{total = sum xs} -> i:Nat -> pre:{pre = sum (take i xs)} 
        -> {v:_ | v = fv xs i} 
  @-}
fv' xs total i pre = abs (pre - post) `withProof` thmSumSplit xs i
  where 
    post           = total - pre 

--------------------------------------------------------------------------------
-- | Lib: Lists, Summing etc. 
--------------------------------------------------------------------------------
drop :: Int -> [a] -> [a]
(++) :: [a] -> [a] -> [a]
take :: Int -> [a] -> [a]

{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {v:[a] | len v = len xs + len ys} @-}
[]     ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)

{-@ reflect take @-}
{-@ take :: Nat -> [a] -> [a] @-}
take 0 _      = [] 
take _ []     = [] 
take n (x:xs) = x : take (n-1) xs  

{-@ reflect drop @-}
{-@ drop :: Nat -> xs:[a] -> {v:[a] | len v <= len xs} @-}
drop 0 xs     = xs 
drop _ []     = []
drop n (_:xs) = drop (n-1) xs 

{-@ reflect sum @-}
sum :: [Int] -> Int 
sum []     = 0 
sum (x:xs) = x + sum xs 

--------------------------------------------------------------------------------
-- Theorems about summing over slices 
--------------------------------------------------------------------------------
thmSumTake  :: [Int] -> Int -> [Int] -> () 
thmSumSplit :: [Int] -> Int -> ()

{-@ thmSumSplit :: xs:[Int] -> i:Nat -> { sum xs = sum (take i xs) + sum (drop i xs) } @-}
thmSumSplit xs i = thmSplitAppend xs i &&& thmSumAppend (take i xs) (drop i xs) 

{-@ type SuffixAt a I Xs = {v:[a] | v = drop I Xs && len v > 0} @-}

{-@ thmSumTake :: xs:[Int] -> i:Nat -> ys:SuffixAt _ i xs -> 
                   { sum (take (i+1) xs) == sum (take i xs) + head ys } 
  @-}   
thmSumTake xs i ys = thmSumAppR (take i xs) (head ys) &&& thmTake xs i ys 

--------------------------------------------------------------------------------
-- Theorems about summing over sequences 
--------------------------------------------------------------------------------
thmSumAppend :: [Int] -> [Int] -> () 
thmSumAppR   :: [Int] -> Int -> () 

{-@ thmSumAppend :: xs:[Int] -> ys:[Int] -> {sum (xs ++ ys) = sum xs + sum ys} @-}
thmSumAppend []     ys = () 
thmSumAppend (x:xs) ys = thmSumAppend xs ys 

{-@ thmSumAppR :: xs:[Int] -> y:Int -> { sum (xs ++ [y]) == sum xs + y } @-}
thmSumAppR []     y = () 
thmSumAppR (x:xs) y = thmSumAppR xs y

--------------------------------------------------------------------------------
-- Theorems about slices 
--------------------------------------------------------------------------------
thmSplitAppend :: [a] -> Int -> () 
thmDrop :: [a] -> Int -> [a] -> () 
thmTake :: [a] -> Int -> [a] -> () 

{-@ thmSplitAppend :: xs:_ -> i:Nat -> { xs == (take i xs) ++ (drop i xs) } @-}
thmSplitAppend xs     0 = () 
thmSplitAppend []     i = () 
thmSplitAppend (x:xs) i = thmSplitAppend xs (i - 1)

-- type SuffixAt a I Xs = {v:[a] | v = drop I Xs && len v > 0} 

{-@ thmDrop :: xs:[a] -> i:Nat -> ys:SuffixAt _ i xs -> { drop (i+1) xs == tail ys } @-}
thmDrop (x:xs) 0 ys = () 
thmDrop []     i ys = thmSuffixAt [] i ys 
thmDrop (x:xs) i ys = thmDrop xs (i-1) ys

{-@ thmTake :: xs:[a] -> i:Nat -> ys:SuffixAt _ i xs -> { take (i+1) xs == (take i xs ++ [head ys]) } @-}
thmTake (x:xs) 0 ys = () 
thmTake []     i ys = thmSuffixAt [] i ys 
thmTake (x:xs) i ys = thmTake xs (i-1) ys

--------------------------------------------------------------------------------
-- Theorems about suffixes
--------------------------------------------------------------------------------
thmSuffix   :: [a] -> Int -> [a] -> () 
thmSuffixAt :: [a] -> Int -> [a] -> () 

{-@ thmSuffix :: xs:[a] -> i:{i > 0} -> ys:SuffixAt _ i xs -> { ys == drop (i-1) (tail xs) } @-}
thmSuffix []     i ys = thmSuffixAt [] i   ys 
thmSuffix (x:xs) 1 ys = () 
thmSuffix (x:xs) i ys = thmSuffix xs (i-1) ys 

{-@ thmSuffixAt :: xs:[a] -> i:Nat -> ys:SuffixAt _ i xs -> { len ys <= len xs} @-} 
thmSuffixAt xs i ys = ys === drop i xs *** QED 

--------------------------------------------------------------------------------
-- | Computing 'argMin' of a Finite Map ----------------------------------------
--------------------------------------------------------------------------------
argMin :: (Ord a) => (Int -> a) -> IMap a -> (Int, Int -> ())
loop   :: (Ord a) => (Int -> a) -> IMap a -> Int -> a -> Int -> (Int -> ()) -> (Int, Int -> ())

{-@ data IMap [size] a <p :: Int -> a -> Bool> =
        Bind { key  :: Int
             , val  :: a<p key>
             , rest :: {v: IMap <p> a | size v = key}
             }
      | Emp
  @-}
data IMap a = Bind Int a (IMap a) | Emp 

{-@ measure size @-}
{-@ size :: IMap a -> Nat @-}
size :: IMap a -> Int 
size Emp          = 0 
size (Bind _ _ m) = 1 + size m

{-@ type GMap a G  = IMap<{\i v -> v = G i}> a   @-}

{-@ argMin :: (Ord a) => g:(Nat -> a) -> m:{GMap a g | size m > 0} -> 
		 (i::Int, j:Int -> {v:() | (btwn 0 j (size m)) => g i <= g j}) 
  @-}
argMin g (Bind k v m) = loop g m k v  (1 + size m) (const ()) 

{-@ loop :: (Ord a) => g:(Nat -> a) 
         -> m0:(GMap a g) -> i0:Int -> v0:{a | v0 = g i0} 
         -> n:Nat 
         -> (j:Int -> {v:() | (btwn (size m0) j n) => g i0 <= g j}) 
         -> (i::Int, j:Int -> {v:() | (btwn 0 j n) => g i  <= g j}) 
  @-}
loop g (Bind i v m) i0 v0 n pf 
  | v < v0             = loop g m i  v  n pf 
  | otherwise          = loop g m i0 v0 n pf 
loop g Emp  i0 v0 n pf = (i0, pf) 

{-@ inline btwn @-}
btwn :: Int -> Int -> Int -> Bool 
btwn lo j hi = lo <= j && j < hi
