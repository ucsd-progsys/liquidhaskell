Measures
========

\begin{comment}
\begin{code}
{-@ LIQUID "--no-termination" @-}
module Ch4 where

import Prelude hiding(null, tail, head)

main = putStrLn "Hello"

-- | Old Definitions

{-@ type Nat     = {v:Int | v >= 0} @-}
{-@ type Pos     = {v:Int | v >  0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

{-@ divide :: Int -> NonZero -> Int @-}
divide     :: Int -> Int -> Int
divide _ 0 = die "divide-by-zero"
divide x n = x `div` n
\end{code}
\end{comment}

\begin{code}
data List a = N | (:+:) a (List a)

infixr 9 :+:

{-@ invariant {v:List a | 0 <= size v} @-}
{-@ measure size @-}
{-@ size :: List a -> Nat @-}
size :: List a -> Int  
size N          = 0
size (_ :+: xs) = 1 + size xs

{-@ type NEList a = {v:List a | size v > 0} @-} 

{-@ head :: NEList a -> a @-} 
head (x :+: _) = x
head N         = die "head: N"

-- EX: what is a signature for `null` such that `safeHead` typechecks
safeHead xs
  | null xs   = Nothing
  | otherwise = Just $ head xs 

{-@ null :: xs:List a -> {v:_ | Prop v <=> size xs = 0} @-}
null N = True
null _ = False

-- SHOW map, foldr, foldr1, wtAverage (BAD), wtAverage (GOOD)

-- EX: risers

-- SHOW zipWith
-- SHOW dotProd
-- SHOW matMult (using dotProd/transpose)

-- EX: write sig for take, drop
-- EX: what is the SIG for reverseHelper s.t. reverse checks?

{-@ reverse :: xs:List a -> ListN a (size xs) @-}
reverse xs = reverseHelper xs N

reverseHelper N acc          = acc
reverseHelper (x :+: xs) acc = reverseHelper xs (x :+: acc)

{- EX: given IMPLEMENTATIONS

   split  :: a -> [a] -> [[a]]
   join   :: a -> [[a]] -> [a]
   assert :: {v:Bool | Prop v} -> a -> a

   WRITE TYPES TO VERIFY:

   prop_join_split str c = assert (size s == size s') ()
     where
        s'               = join c (split s c)
 -}

{-@ type ListN a N = {v:List a | size v = N} @-}

{-@ type Grid a N M = ListN (ListN a M) N    @-}

{- EX: write a function

   transpose :: n:Nat -> m:Nat -> Grid a n m -> Grid a m n
-}

{- EX: write a function kmeans (using map-reduce) -}

\end{code}

LINKS 
+ Case Study 1: AlphaConvert (tests/pos/alphaconvert-List.hs) 

+ Case Study 2: Kmeans

