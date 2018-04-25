{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ infixr ++              @-}
{-@ infixr !!              @-}

module PadLeft where 

import Prelude hiding (replicate, (++), (!!))
import Language.Haskell.Liquid.NewProofCombinators 

-----------------------------------------------------------------------------------
-- Code 
-----------------------------------------------------------------------------------
{-@ reflect padLeft @-}
padLeft :: Int -> a -> [a] -> [a]
padLeft n c xs 
  | size xs < n = replicate (n - size xs) c ++ xs 
  | otherwise   = xs 

-----------------------------------------------------------------------------------
-- Properties 
-----------------------------------------------------------------------------------
{-@ thmPadLeft :: n:_ -> c:_ -> xs:{size xs < n} -> 
                    i:Nat -> { (padLeft n c xs !! i) == (if (i < n - size xs) then c else (xs !! (i - (n - size xs)))) }                               
  @-}
thmPadLeft :: Int -> a -> [a] -> Int -> ()
thmPadLeft n c xs i 
  | i < n - size xs = thmAppLeft  (replicate (n - size xs) c) xs i &&& thmReplicate (n - size xs) c i   
  | otherwise       = thmAppRight (replicate (n - size xs) c) xs i

-----------------------------------------------------------------------------------
-- Theorems about Lists (these are baked in as 'axioms' in the dafny prelude) 
-- https://github.com/Microsoft/dafny/blob/master/Binaries/DafnyPrelude.bpl#L896-L1108
-----------------------------------------------------------------------------------

{-@ thmAppLeft :: xs:[a] -> ys:[a] -> {i:Nat | i < size xs} -> { (xs ++ ys) !! i == xs !! i } @-} 
thmAppLeft :: [a] -> [a] -> Int -> ()
thmAppLeft (x:xs)  ys 0 = () 
thmAppLeft (x:xs) ys i  = thmAppLeft xs ys (i-1)      

{-@ thmAppRight :: xs:[a] -> ys:[a] -> {i:Nat | size xs <= i} -> { (xs ++ ys) !! i == ys !! (i - size xs) } @-} 
thmAppRight :: [a] -> [a] -> Int -> ()
thmAppRight []     ys i = () 
thmAppRight (x:xs) ys i = thmAppRight xs ys (i-1)      

{-@ thmReplicate :: n:Nat -> c:a -> i:{Nat | i < n} -> { replicate n c !! i  == c } @-}
thmReplicate :: Int -> a -> Int -> () 
thmReplicate n c i 
  | n == 0    = () 
  | i == 0    = ()
  | otherwise = thmReplicate (n-1) c (i-1) 

-----------------------------------------------------------------------------------
-- Stuff from library Data.List 
-----------------------------------------------------------------------------------

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> a -> {v:[a] | size v = n} @-}
replicate :: Int -> a -> [a]
replicate 0 _ = [] 
replicate n c = c : replicate (n - 1) c

{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {v:[a] | size v = size xs + size ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0 
size (x:xs) = 1 + size xs

{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> {n:Nat | n < size xs} -> a @-}
(!!) :: [a] -> Int -> a 
(x:_)  !! 0 = x 
(_:xs) !! n = xs !! (n - 1)

-----------------------------------------------------------------------------------