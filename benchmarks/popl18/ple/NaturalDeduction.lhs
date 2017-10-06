Natural Deduction on Liquid Haskell 
------------------------------------

We illustrate the encoding 
natural deduction in Liquid Haskell. 
It is a formed versions of § 3.3 of 
["Towards Complete Specification and Verification with SMT"](https://nikivazou.github.io/static/popl18/refinement-reflection.pdf).


Prelude
--------
To use Liquid Haskell as a higher order theorem prover 
you need to enable the `higherorder` flag 
(for efficiency it is off by default)
and import the [`ProofCombinators`](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/ProofCombinators.hs)
library.

\begin{code}
module NaturalDeduction where

{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding ((++), length)
{-@ infix   ++ @-}
\end{code}


Natural Deduction as Type Derivation
------------------------------------

We illustrate the mapping from natural deduction rules to
typing rules in the below figure  which uses typing judgments to express Gentzen’s proof of the proposition

<br>
<center>
`ϕ ≡ (∃x.∀y.(p x y)) ⇒ (∀y.∃x.(p x y))`

<img src="http://goto.ucsd.edu/~nvazou/images/reflect-figure4.png" height="200" align="middle" />

</center>
<br>


Read bottom-up, the derivation provides a proof of `ϕ`. 
Read top-down, it constructs a proof of the
formula as the term `λe y.case e of {(x, ex ) → (x, ex y)}`. 
This proof term corresponds directly to
the following Haskell expression that typechecks with type `ϕ`.

\begin{code}
{-@ exAll :: p:(a -> a -> Bool)
          -> (x::a, y:a -> {v:Proof | p x y}) 
          -> y:a 
          -> (x::a, {v:Proof | p x y}) @-}
exAll :: (a -> a -> Bool) -> (a, a -> Proof) -> a -> (a, Proof) 
exAll p = \e y -> case e of {(x, ex) -> (x, ex y)}
\end{code}



SMT-aided proofs 
----------------

The great benefit of using refinement types to encode natural deduction is
that quantifier-free portions of the proof can get automated via SMTs. 
For every quantifier-free proposition `ϕ`, you can convert between `{ϕ}`, 
where `ϕ` is treated as an SMT-proposition and `ϕ`, 
where `ϕ` is treated as a type; 
and this conversion goes both ways. 
For example, let `ϕ ≡ p ∧ (q||r)`. 
Then flatten converts from `ϕ` to `{ϕ}` and expand the other way, 
while this conversion is SMT-aided.

\begin{code}
{-@ flatten :: p:Bool -> q:Bool -> r:Bool 
           -> ({v:Bool | p }, Either {v:Bool | q } {v:Bool | r}) 
           -> {proof:Bool | p && (q || r)} @-}
flatten :: Bool -> Bool -> Bool -> (Bool, Either Bool Bool) -> Bool 
flatten _ _ _ (pf, Left  qf) = pf && qf
flatten _ _ _ (pf, Right rf) = pf && rf

{-@ expand :: p:Bool -> q:Bool -> r:Bool 
           -> {proof:Bool | p && (q || r)} 
           -> ({v:Bool | p }, Either {v:Bool | q } {v:Bool | r}) @-}
expand :: Bool -> Bool -> Bool -> Bool -> (Bool, Either Bool Bool) 
expand p q r proof | q = (proof, Left  proof) 
expand p q r proof | r = (proof, Right proof) 
\end{code}

Distributing Quantifiers
------------------------

Next, we construct the proof terms needed to prove two logical properties:
that existentials distribute over disjunctions and foralls over conjunctions, 
i.e.

<br>
<center>
`ϕ∃ ≡ (∃x.p x ∨ q x) ⇒ ((∃x.p x) ∨ (∃x.q x))` (1)
<br>
`ϕ∀ ≡ (∀x.p x ∧ q x) ⇒ ((∀x.p x) ∧ (∀x.q x))` (2)
</center>
<br>

The specification of these properties requires nesting quantifiers inside 
connectives and vice versa.
The proof of `ϕ∃` (1) proceeds by existential case splitting and introduction:

\begin{code}
{-@ exDistOr :: p : _ -> q : _
             -> (x :: a ,Either {v:b | p x } {v:c | q x })
             -> Either (x::a , {v:b | p x }) (x::a , {v:c | q x }) @-}
exDistOr :: (a -> Bool) -> (a -> Bool) -> (a, Either c d) -> Either (a, c) (a,d)
exDistOr _ _ (x , Left px ) = Left (x , px )
exDistOr _ _ (x , Right qx ) = Right (x , qx )
\end{code}

Dually, we prove `ϕ∀` (2) via a λ-abstraction and case spitting 
inside the conjunction pair:

\begin{code}
{-@ allDistAnd :: p:_ -> q:_ 
               -> (x:a -> ({v:b | p x }, {v:c| q x}))
               -> ((x:a -> {v:b | p x }), (x:a -> {v:c| q x })) @-}
allDistAnd :: (a -> Bool) -> (a -> Bool) -> (a -> (b,c)) -> (a -> b, a -> c)
allDistAnd _ _ andx = 
    ((\x -> case andx x of (px, _ ) -> px)
    ,(\x -> case andx x of (_ , qx) -> qx) 
    )
\end{code}

The above proof term corresponds to its natural deduction 
proof derivation but using
SMT-aided verification can get simplified to the following

\begin{code}
{-@ allDistAnd' :: p:_ -> q:_ 
               -> (x:a -> ({v:Bool | p x }, {v:Bool| q x}))
               -> ((x:a -> {v:Bool | p x }), (x:a -> {v:Bool| q x })) @-}
allDistAnd' :: (a -> Bool) -> (a -> Bool) -> (a -> (Bool,Bool)) 
            -> (a -> Bool, a -> Bool)
allDistAnd' _ _ andx = (pf, pf)
  where pf x = case andx x of (px,py) -> px && py
\end{code}



Properties of User Defined Datatypes 
------------------------------------

As `ϕ` can describe properties of data types like lists, 
we can prove properties of such types, 
e.g. that for every list `xs`, 
if there exists a list `ys` such that
`xs == ys ++ ys` ,then `xs` has even length.

<br>
<center>
`ϕ ≡ ∀xs.((∃ys. xs = ys ++ ys) ⇒ (∃n.length xs = n + n))`
</center>
<br>

The proof (`evenLen`) proceeds by existential elimination and introduction.
and uses the `lenAppend` lemma.

\begin{code}
{-@ evenLen :: xs:_ 
            -> (ys::L a, {v:Proof |  xs = ys ++ ys }) 
            -> (n ::Int, {v:Proof | length xs = n + n }) @-}
evenLen :: L a -> (L a, Proof) -> (Int, Proof)
evenLen xs (ys, pf) = (length ys, lenAppend ys ys &&& pf )
\end{code}

The `lenAppend` lemma
is proved by induction on the input list and PLE to automate 
equational reasoning.

\begin{code}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ lenAppend :: xs : L a -> ys : L a 
              -> { length ( xs ++ ys ) = length xs + length ys } @-}
lenAppend :: L a -> L a -> Proof
lenAppend N        _  = trivial 
lenAppend (C x xs) ys = lenAppend xs ys
\end{code}

Lists in the above proof are used defined inductive 
data types whose `length` is decreasing at each recursive call.

\begin{code}
data L a = N | C a (L a)
{-@ data L [length] a = N | C {hd :: a, tl :: L a} @-}

length :: L a -> Int 
{-@ length :: x:L a -> {v:Nat | v == length x} @-}
{-@ measure length @-}
length N        = 0 
length (C _ xs) = 1 + length xs 
\end{code}

The appending function `(++)`
is Haskell's usual append reflected in the logic.
\begin{code}
{-@ reflect ++ @-}
N        ++ ys = ys 
(C x xs) ++ ys = C x (xs ++ ys)
\end{code}



Induction on Natural Numbers
----------------------------

Finally, we specify and verify induction on natural numbers:

<br>
<center>
`ϕind ≡ (p 0 ∧ (∀n.p (n − 1) ⇒ p n) ⇒ ∀n.p n)`
</center>
<br>

The proof proceeds by induction (e.g. case splitting). 
In the base case, `n == 0`, 
the proof calls the left conjunct, 
which contains a proof of the base case. 
Otherwise, `0 < n`, the proof applies the induction
hypothesis to the right conjunct instantiated at `n-1`.

\begin{code}
{-@ ind :: p:_ 
        -> ({v:Proof| p 0}, (n:Nat -> {v:Proof | p (n-1)} -> {v:Proof | p n})) 
        -> n:Nat 
        -> {v:Proof | p n} @-}
ind :: (Int -> Bool) -> (Proof, Int -> Proof -> Proof) -> Int -> Proof 
ind p (p0, pn) n 
  | n == 0    = p0
  | otherwise = pn n (ind p (p0, pn) (n-1))
\end{code}
