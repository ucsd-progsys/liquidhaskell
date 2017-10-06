Overview
------------------------------------

We illustrate Liquid Haskell as a theorem prover. 
It is a formed version of § 2 of 
["Towards Complete Specification and Verification with SMT"](https://nikivazou.github.io/static/popl18/refinement-reflection.pdf).


Prelude 
--------

Overview is a Haskell module with Liquid Haskell annotations. 
We enable the Liquid Haskell flags that allow 
higher order reasoning
(which is increasing the precision of verification and is by default off for efficiency).
By default Liquid Haskell checks that all your functions are total. 

\begin{code}
module Overview where
{-@ LIQUID "--higherorder"    @-}

import Language.Haskell.Liquid.ProofCombinators 
\end{code}

2.1 Refinement Types
---------------------


Propositions with SMT-automated proofs 

\begin{code}
{-@ type Plus_2_2 = {v:Proof | 2 + 2 = 4 } @-}

plus_2_2 :: () -> Proof 
{-@ plus_2_2 :: () -> Plus_2_2 @-}
plus_2_2 _ = () 

{-@ type Plus_comm = x:Int -> y:Int -> {v:Proof | x + y = y + x } @-}
plus_comm :: Int -> Int -> Proof 
plus_comm _ _ = () 

{-@ type Int_up = n:Int -> (m::Int, {v:Proof | n < m}) @-}
{-@ int_up :: Int_up @-}
int_up :: Int -> (Int, Proof)
int_up n = (n+1, ()) 
\end{code}

*Note:*
In the paper we defined `plus_2_2` 
to take zero arguments, while here we give it a unit argument. 
The reason is to keep verification local. 
If we define a zero argument proof term, 
the property it is proving will 
be checked but then will enter in the assumption 
environment that proves the rest of the module. 
For example, the following property (commented out) 
will get verified as unsafe

\begin{code}
{- 
false     :: Proof 
{-@ false :: {v:Proof | false} @-}
false     = ()  
-}
\end{code}

but then verification of the rest of the module 
will assume false. 
This is sound, but inconvenient. 
Thus, we follow the convention not to have proof terms without 
arguments. 


2.2 Refinement Reflection
--------------------------

We define the function `fib` on natural numbers 
and reflect it into logic. 

\begin{code}
{-@ reflect fib @-}
{-@ fib :: Nat -> Nat @-}
fib :: Int -> Int
fib i | i <= 1 = i 
fib i = fib (i-1) + fib (i-2)
\end{code}

To prove that `fib 2 == 1` we need to call `fib` on 
arguments, `0`, `1`, and `2`.
\begin{code}
{-@ pf_fib2 :: { v:_ | fib 2 = 1 } @-}
pf_fib2 :: (Int,Int,Int)
pf_fib2 = let { t0 = fib 0; t1 = fib 1; t2 = fib 2 } 
          in (t0,t1,t2)
\end{code}

Unlike the paper, we return the results `t0`, `t1`, and `t2`.
If we do not return these calls, ghc will optimize them away, 
to Liquid Haskell will not see these calls. 
Thus the `pf_fib2` version presented in the paper:

< {-@ pf_fib2Unsafe  :: () -> { v:_ | fib 2 = 1 } @-}
< pf_fib2Unsafe      :: () -> Proof 
< pf_fib2Unsafe _    = let { t0 = fib 0; t1 = fib 1; t2 = fib 2 } 
<                      in ()

In unsafe, since Liquid Haskell just sees 

< pf_fib2Unsafe _ = ()

Alternative, we could write 

\begin{code}
{-@ pf_fib2' :: () -> {v:[Nat] | fib 2 = 1 } @-}
pf_fib2'     :: () -> [Int]
pf_fib2' _   =  [ fib 0 , fib 1 , fib 2 ]
\end{code}

2.3 Equational Proofs
----------------------

We structure proofs using 
proof combinators from the imported 
[ProofCombinators](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/ProofCombinators.hs) library, that comes with Liquid Haskell.

- **“Equation” Combinators**
Using the `(==.)` equational operator, 
the proof `fib2_1` is formatted as below. 

\begin{code}
fib2_1     :: () -> Proof 
{-@ fib2_1 :: () -> { fib 2 = 1 } @-}
fib2_1 _   
  =   fib 2 
  ==. fib 1 + fib 0 
  ==. 1 
  *** QED
\end{code}

*Note:* the operator `==.` takes two terms to be proved equal 
and one *optional* proof argument. 
You can check its definition at the library  
[ProofCombinators](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/ProofCombinators.hs)


Also, the intermediate steps of the proofs are not checked. 
For example, the following proof is verified, even if the intermediate equality 
steps are not correct

\begin{code}
fib2_1'     :: () -> Proof 
{-@ fib2_1' :: () -> { fib 2 = 1 } @-}
fib2_1' _   
  =   fib 2 
  ==. fib 1 + fib 0 
  ==. fib 8 + fib 1 
  ==. 1 
  *** QED
\end{code}

- **“Because” Combinators**
To prove `fib 3 = 2` we call the proof `fib2_1` as a lemma
using the `(?)` combinator. 

\begin{code}
fib3_2     :: () -> Proof
{-@ fib3_2 :: () -> { fib 3 = 2 } @-}
fib3_2 _ 
  =   fib 3 
  ==. fib 2 + fib 1 
  ==. 2             ? (fib2_1 ())
  *** QED
\end{code}

- **Arithmetic and Ordering**
Similarly, we use arithmetic proof combinators 
for arithmetic proofs. 

\begin{code}
fibUp :: Int -> Proof 
{-@ fibUp :: n:Nat -> {fib n <= fib (n + 1)} @-}
fibUp 0 
  = fib 0  <. fib 1 *** QED
fibUp 1 
  = fib 1 <=. fib 1 + fib 0 ==. fib 2 *** QED
fibUp n 
  = fib n <=. fib n + fib (n-1) ==. fib (n+1) *** QED
\end{code}

- **Induction & Higher Order Reasoning**
Our technique reasons about higher order properties too, 
that is, we can prove theorems over any function `f`. 
For example, we prove that every function 
`f` that increases locally 
(i.e. `f z ≤ f (z+1)` for all `z`) 
also increases globally (i.e. `f x ≤ f y` for all `x < y`)

\begin{code}
fMono :: (Int -> Int)
      -> (Int -> Proof)
      -> Int -> Int
      -> Proof
{-@ fMono :: f:(Nat -> Int) 
          -> (n:Nat -> {f n <= f (n + 1)})
          -> x:Nat -> y:{Nat | x < y} 
          ->  {f x <= f y} / [y] @-}
fMono f up x y
  | x+1 == y 
  = f x <=. f (x+1) ? up x 
        <=. f y 
        *** QED
  | x+1 <  y 
  = f x <=. f (y-1) ? fMono f up x (y-1) 
        <=. f y     ? up (y-1) 
        *** QED
\end{code}

We prove the theorem by induction on `y` as specified by the annotation 
`/ [y]` which states that
`y` is a well-founded termination metric that decreases at each recursive call.

We can apply the general `fMono` theorem to prove that 
`fib` increases monotonically:

\begin{code}
fibMono :: Int -> Int -> Proof
{-@ fibMono :: n:Nat -> m:{Nat |  n < m } -> { fib n <= fib m } @-}
fibMono = fMono fib fibUp
\end{code}


2.4 Complete Verification: Automating Equational Reasoning
-----------------------------------------------------------
Next, we use PLE to automate our proofs. 
The local `automatic-instances` flag activates PLE 
on functions that are marked with `automatic-instances`

\begin{code}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
\end{code}

With these flags (as thus PLE) activated, 
the proof terms as simplified to only use 
recursive calls and helper lemmata. 

\begin{code}
{-@ automatic-instances fib3_2_PLE @-}
fib3_2_PLE     :: () -> Proof
{-@ fib3_2_PLE :: () -> { fib 3 = 2 } @-}
fib3_2_PLE _   =  ()
\end{code}


\begin{code}
{-@ automatic-instances fibUpPLE @-}
fibUpPLE :: Int -> Proof 
{-@ fibUpPLE :: n:Nat -> {fib n <= fib (n + 1)} @-}
fibUpPLE 0 = ()
fibUpPLE 1 = ()
fibUpPLE n = fibUp (n-1) &&& fibUp (n-2)
\end{code}


\begin{code}
fMonoPLE :: (Int -> Int)
      -> (Int -> Proof)
      -> Int -> Int
      -> Proof
{-@ fMonoPLE :: f:(Nat -> Int) 
          -> (n:Nat -> {f n <= f (n + 1)})
          -> x:Nat -> y:{Nat | x < y} 
          ->  {f x <= f y} / [y] @-}
fMonoPLE f up x y
  | x+1 == y 
  = up x 
  | x+1 <  y 
  =   fMonoPLE f up x (y-1) 
  &&& up (y-1) 
\end{code}
