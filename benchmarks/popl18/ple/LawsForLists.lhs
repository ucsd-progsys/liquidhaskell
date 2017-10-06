Laws for Lists
------------------------------------

We illustrate a case study for Liquid Haskell as a theorem prover, 
by proving the standard laws for lists. 
It is a formed versions of § 2.5 of 
["Towards Complete Specification and Verification with SMT"](https://nikivazou.github.io/static/popl18/refinement-reflection.pdf).


Prelude 
--------

Overview is a Haskell module with Liquid Haskell annotations. 
We enable the Liquid Haskell flags that allow 
higher order reasoning and the reflection of all user-defined ADTs into the logic
(both features are increasing the precision of verification and are off for efficiency).
We also enable PLE globally, to automatically prove all the theorems.
By default Liquid Haskell checks that all your functions are total. 

\begin{code}
module LawsForLists where
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

{-@ LIQUID "--automatic-instances=liquidinstances" @-}

import Language.Haskell.Liquid.ProofCombinators 

import Prelude hiding (length, head, tail, map, (++))
\end{code}


First, we define a user-defined list with a termination metric `length`.

\begin{code}
data L a = N | C {hd :: a, tl :: L a}
{-@ data L [length] a = N | C {hd :: a, tl :: L a} @-}

length :: L a -> Int 
{-@ length :: L a -> Nat @-}
{-@ measure length @-}
length N        = 0 
length (C _ xs) = 1 + length xs  
\end{code}

Next, we define and reflect function composition and 
the standard list map and append functions. 

\begin{code}
{-@ infix   o @-}
{-@ reflect o @-}
o f g x = f (g x)
\end{code}

\begin{code}
{-@ reflect map @-}
map :: (a -> b) -> L a -> L b 
map _ N        = N 
map f (C x xs) = f x `C` map f xs 
\end{code}


\begin{code}
{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: L a-> L a -> L a 
N        ++ ys = N 
(C x xs) ++ ys = C x (xs ++ ys) 
\end{code}

Finally, we use PLE to automatically prove the properties on lists.

- Append Nil Identity 

\begin{code}
appendNilId     :: L a -> Proof
{-@ appendNilId ::  xs:_ -> { xs ++ N = xs } @-}
appendNilId N        = () 
appendNilId (C _ xs) = appendNilId xs  
\end{code}

- Append Associative 
\begin{code}
appendAssoc :: L a -> L a -> L a -> Proof
{-@ appendAssoc :: xs:_ -> ys:_ -> zs:_ -> { xs ++ (ys ++ zs) = (xs ++ ys) ++ zs } @-}
appendAssoc N _ _          = ()
appendAssoc (C _ xs) ys zs = appendAssoc xs ys zs
\end{code}

- Map Fusion 
\begin{code}
{-@ mapFusion :: f:_ -> g:_ -> xs:_ -> { map (f o g) xs = map (f o g) xs } @-}
mapFusion f g N = ()
mapFusion f g (C _ xs) = mapFusion f g xs 
\end{code}

- Swapping 

\begin{code}
{-@ reflect swap @-}
swap :: Ord a => L a  -> L a
swap (C x1 (C x2 xs)) 
  | x1 > x2 
  = C x2 (C x1 xs)
  | otherwise 
  = C x1 (C x2 xs)
swap xs = xs
\end{code}

\begin{code}
swapIdemp :: L Int -> Proof 
{-@ swapIdemp :: xs:L Int -> {swap (swap xs) = swap xs } @-} 
swapIdemp (C x1 (C x2 xs)) 
  | x1 > x2   = ()
  | otherwise = () 
swapIdemp xs  = () 
\end{code}