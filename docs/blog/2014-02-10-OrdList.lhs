---
layout: post
title: "OrdList"
date: 2014-02-10
author: Eric Seidel
published: true
comments: true
external-url:
categories: basic measures
demo: OrdList.hs
---

This morning someone asked on [Reddit][] how one might define [OrdList][] in
order to statically ensure its three key invariants. The accepted
solution required rewriting `OrdList` as a `GADT` indexed by a proof of
*emptiness*, and used the new Closed Type Families extension in GHC
7.8 to define a type-level join of the Emptiness index. Let's see how
to tackle this problem in LiquidHaskell, without changing a single
line of code (well.. maybe one)!

[Reddit]: http://www.reddit.com/r/haskell/comments/1xiurm/how_to_define_append_for_ordlist_defined_as_gadt/
[OrdList]: http://www.haskell.org/platform/doc/2013.2.0.0/ghc-api/OrdList.html

<div class="hidden">
\begin{code}
module OrdList(
    OrdList, 
        nilOL, isNilOL, unitOL, appOL, consOL, snocOL, concatOL,
        mapOL, fromOL, toOL, foldrOL, foldlOL, foldr', concatOL'
) where

infixl 5  `appOL`
infixl 5  `snocOL`
infixr 5  `consOL`
-- UGH parsing issues...
{-@
data OrdList [olen] a = None
                      | One  (x  :: a)
                      | Many (xs :: ListNE a)
                      | Cons (x  :: a)           (xs :: OrdList a)
                      | Snoc (xs :: OrdList a)   (x  :: a)
                      | Two  (x  :: OrdListNE a) (y  :: OrdListNE a)
@-}
\end{code}
</div>

\begin{code}
data OrdList a
  = None
  | One a
  | Many [a]        -- Invariant: non-empty
  | Cons a (OrdList a)
  | Snoc (OrdList a) a
  | Two (OrdList a) -- Invariant: non-empty
        (OrdList a) -- Invariant: non-empty
\end{code}

Here's the definition of `OrdList`, the key invariants are that
`Many` takes a *non-empty* list and that `Two` takes two non-empty
`OrdList`s. In LiquidHaskell we can specify the invariants as
\begin{code} part of the data declaration, like so
{-@
data OrdList [olen] a
  = None
  | One  (x  :: a)
  | Many (xs :: ListNE a)
  | Cons (x  :: a)           (xs :: OrdList a)
  | Snoc (xs :: OrdList a)   (x  :: a)
  | Two  (x  :: OrdListNE a) (y  :: OrdListNE a)
@-}
\end{code}

The important bits in this definition are the `ListNE` and
`OrdListNE` type aliases, which specify that the lists must not be empty.

\begin{code}
{-@ type ListNE    a   = {v:[a]       | (len v)  > 0} @-}
{-@ type OrdListNE a   = {v:OrdList a | (olen v) > 0} @-}
\end{code}

We've previously seen the definition of `len`, but `olen` is of
course new.

\begin{code}
{-@
measure olen :: OrdList a -> Int
olen (None)      = 0
olen (One x)     = 1
olen (Many xs)   = (len xs)
olen (Cons x xs) = 1 + (olen xs)
olen (Snoc xs x) = 1 + (olen xs)
olen (Two x y)   = (olen x) + (olen y)
@-}

{-@ invariant {v:OrdList a | (olen v) >= 0} @-}
\end{code}

Nothing out of the ordinary here either. Now let's look at some of
the functions!

\begin{code}
{-@ type OrdListN a N = {v:OrdList a | (olen v) = N} @-}

{-@ nilOL   :: OrdListN a {0} @-}
{-@ isNilOL :: xs:OrdList a
            -> {v:Bool | ((Prop v) <=> ((olen xs) = 0))}
  @-}

{-@ unitOL :: a -> OrdListN a {1} @-}

{-@ snocOL :: xs:OrdList a -> a
           -> OrdListN a {1 + (olen xs)}
  @-}
{-@ consOL :: a -> xs:OrdList a
           -> OrdListN a {1 + (olen xs)}
  @-}
{-@ appOL  :: xs:OrdList a -> ys:OrdList a
           -> OrdListN a {(olen xs) + (olen ys)}
  @-}

nilOL            = None
unitOL as        = One as
snocOL as   b    = Snoc as b
consOL a    bs   = Cons a bs

isNilOL None = True
isNilOL _    = False

None  `appOL` b     = b
a     `appOL` None  = a
One a `appOL` b     = Cons a b
a     `appOL` One b = Snoc a b
a     `appOL` b     = Two a b
\end{code}

Notice that we've given very precise types here, e.g. `unitOL`
returns an `OrdList` with one element, `snocOL` and `consOL` return
lists with precisely one more element, and `appOL` returns a list
whose length is the sum of the two input lists. (Aside: the `OrdListN a
{foo}` syntax just lets us use LiquidHaskell expressions as
arguments to type aliases.) The most important thing to notice,
however, is that we haven't had to insert any extra checks in
`appOL`, unlike the [GADT][] solution. LiquidHaskell uses the definition
of `olen` to infer that in the last case of `appOL`, `a` and `b`
*must* be non-empty, so they are valid arguments to `Two`.

[GADT]: http://www.reddit.com/r/haskell/comments/1xiurm/how_to_define_append_for_ordlist_defined_as_gadt/cfbrinr

We can prove other things about `OrdList`s as well, like the fact
that converting an `OrdList` to a Haskell list preserves length

\begin{code}
{-@ toOL :: xs:[a] -> OrdListN a {(len xs)} @-}
toOL [] = None
toOL xs = Many xs
\end{code}

as does mapping over an `OrdList`

\begin{code}
{-@ mapOL :: (a -> b) -> xs:OrdList a
          -> OrdListN b {(olen xs)}
  @-}
mapOL _ None        = None
mapOL f (One x)     = One (f x)
mapOL f (Cons x xs) = Cons (f x) (mapOL f xs)
mapOL f (Snoc xs x) = Snoc (mapOL f xs) (f x)
mapOL f (Two x y)   = Two (mapOL f x) (mapOL f y)
mapOL f (Many xs)   = Many (map f xs)
\end{code}

as does converting a Haskell list to an `OrdList`

\begin{code}
{-@ type ListN a N = {v:[a] | (len v) = N} @-}

{-@ fromOL :: xs:OrdList a -> ListN a {(olen xs)} @-}
fromOL a = go a []
  where
    go None       acc = acc
    go (One a)    acc = a : acc
    go (Cons a b) acc = a : go b acc
    go (Snoc a b) acc = go a (b:acc)
    go (Two a b)  acc = go a (go b acc)
    go (Many xs)  acc = xs ++ acc
\end{code}

though for this last one we actually need to provide an explicit
qualifier, which we haven't really seen so far. Can anyone guess why?



\begin{code}
{-@ qualif Go(v:List a, xs:OrdList a, ys:List a):
      (len v) = (olen xs) + (len ys)
  @-}
\end{code}

The answer is that the return type of `go` must refer to the length
of the `OrdList` that it's folding over *as well as* the length of
the accumulator `acc`! We haven't written a refinement like that in
any of our type signatures in this module, so LiquidHaskell doesn't
know to guess that type.

There's nothing super interesting to say about the `foldOL`s but I'll
include them here for completeness' sake.

\begin{code}
foldrOL :: (a->b->b) -> b -> OrdList a -> b
foldrOL _ z None        = z
foldrOL k z (One x)     = k x z
foldrOL k z (Cons x xs) = k x (foldrOL k z xs)
foldrOL k z (Snoc xs x) = foldrOL k (k x z) xs
foldrOL k z (Two b1 b2) = foldrOL k (foldrOL k z b2) b1
foldrOL k z (Many xs)   = foldr k z xs

foldlOL :: (b->a->b) -> b -> OrdList a -> b
foldlOL _ z None        = z
foldlOL k z (One x)     = k z x
foldlOL k z (Cons x xs) = foldlOL k (k z x) xs
foldlOL k z (Snoc xs x) = k (foldlOL k z xs) x
foldlOL k z (Two b1 b2) = foldlOL k (foldlOL k z b1) b2
foldlOL k z (Many xs)   = foldl k z xs
\end{code}

Now, the astute readers will have probably noticed that I'm missing
one function, `concatOL`... We can give `concatOL` a precise type in
LiquidHaskell, but we're actually going to have to inline the `foldr`

\begin{code}
{-@
measure olens :: [OrdList a] -> Int
olens ([])     = 0
olens (ol:ols) = (olen ol) + (olens ols)
@-}

{-@ invariant {v:[OrdList a] | (olens v) >= 0} @-}

{-@ concatOL :: xs:[OrdList a] -> OrdListN a {(olens xs)} @-}
concatOL []       = None
concatOL (ol:ols) = ol `appOL` concatOL ols
\end{code}

This type says that `concatOL` returns an `OrdList` whose length is
the *sum* of the lengths of the input lists, and LiquidHaskell is
happy to verify it, again with no sign of explicit proofs. This is
actually a great illustration of the flexibility provided by
*measures*. Instead of having to encode everything into a massive,
super-index, we are able to split our properties out into independent
*views* of the datatype. I would argue that this approach is much
more modular, as I didn't have to go back and change the definition
of `[]` to talk about `OrdList`s, nor did I have to provide an
explicit witness of the length.


<div class="hidden">
We can actually even verify the original definition of `concatOL` with a
clever use of *abstract refinements*, but we have to slightly change
the signature of `foldr`.

\begin{code}
{- UGH CAN'T PARSE `GHC.Types.:`...
foldr' :: forall <p :: [a] -> b -> Prop>.
          (xs:[a] -> x:a -> b<p xs> -> b<p (GHC.Types.: x xs)>)
       -> b<p GHC.Types.[]>
       -> ys:[a]
       -> b<p ys>
@-}
foldr' f z []     = z
foldr' f z (x:xs) = f xs x (foldr' f z xs)
\end{code}

We've added a *ghost parameter* to the folding function, letting us
refer to the tail of the list at each folding step. This lets us
encode inductive reasoning in the type of `foldr`, specifically that

1. given a base case `z` that satisfies `p []`
2. and a function that, given a value that satisfies `p xs`, returns
a value satisfying `p (x:xs)`
3. the value returned by `foldr f z ys` must satisfy `p ys`!

LiquidHaskell can use this signature, instantiating `p` with `\xs
-> {v:OrdList a | (olen v) = (olens xs)}` to prove the original
definition of `concatOL`!

\begin{code}
{-@ concatOL' :: xs:[OrdList a] -> OrdListN a {(olens xs)} @-}
concatOL' aas = foldr' (const appOL) None aas
\end{code}

We haven't added the modified version of `foldr` to the LiquidHaskell
Prelude yet because it adds the ghost variable to the Haskell
type-signature.
</div>
