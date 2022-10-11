{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ infixr ++              @-}
{-@ infixr !!              @-}

module PadLeft where

import Prelude hiding (max, replicate, (++), (!!))

-----------------------------------------------------------------------------------
-- | Code 
-----------------------------------------------------------------------------------
{-@ reflect leftPad @-}
{-@ leftPad :: n:Int -> c:a -> xs:[a] -> {v:[a] | size v = max n (size xs)} @-}
leftPad :: Int -> a -> [a] -> [a]
leftPad n c xs 
  | 0 < pad   = replicate pad c ++ xs 
  | otherwise = xs 
  where 
    pad       = n - size xs

{-@ leftPadObvious :: n:Int -> c:a -> xs:[a] -> 
      { leftPad n c xs = if (size xs < n) 
                            then (replicate (n - size xs) c ++ xs) 
                            else xs 
      } 
  @-}
leftPadObvious :: Int -> a -> [a] -> () 
leftPadObvious n _ xs = if size xs < n then () else ()

{-@ reflect max @-}
max :: Int -> Int -> Int 
max x y = if x > y then x else y 

-----------------------------------------------------------------------------------
-- Properties 
-----------------------------------------------------------------------------------
{-@ thmLeftPad :: n:_ -> c:_ -> xs:{size xs < n} -> 
                    i:{Nat | i < n} -> { (leftPad n c xs !! i) == (if (i < n - size xs) then c else (xs !! (i - (n - size xs)))) }                               
  @-}
thmLeftPad :: Int -> a -> [a] -> Int -> ()
thmLeftPad n c xs i 
  | i < k     = thmAppLeft  cs xs i `seq` thmReplicate k c i   
  | otherwise = thmAppRight cs xs i
  where 
    k         = n - size xs 
    cs        = replicate k c

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
  | i == 0    = ()
  | otherwise = thmReplicate (n-1) c (i-1) 

-- Stuff from library Data.List 

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
