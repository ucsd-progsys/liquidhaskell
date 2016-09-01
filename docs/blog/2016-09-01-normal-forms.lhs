---
layout: post
title: "Normal Forms"
date: 2016-09-05
comments: true
external-url:
author: Ranjit Jhala
published: true
categories: measures
demo: ANF.hs
---

I have been preparing an undergraduate course on
Compilers in which we build a compiler that crunches
an ML-like language to X86 assembly.
One of my favorite steps in the compilation is the
[conversion to A-Normal Form (ANF)][anf-felleisen]
where, informally speaking, each call or primitive
operation's arguments are **immediate** values,
i.e. constants or variable lookups whose values can
be loaded with a single machine instruction. For example,
the expression

```haskell
((2 + 3) * (12 - 4)) * (7 + 8)
```

has the A-Normal Form:

```haskell
"let anf0 = 2 + 3
     anf1 = 12 - 4
     anf2 = anf0 * anf1
     anf3 = 7 + 8
  in
    anf2 * anf3
```

The usual presentation of ANF conversion
is very elegant but relies upon a clever
use of [continuations][anf-might].
Lets look at another perhaps simpler approach,
where we can use refinements to light the way.

<!-- more -->

<div class="hidden">
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--total"          @-}

module ANF (Op (..), Expr (..), isImm, isAnf, toAnf) where

import Control.Monad.State.Lazy

mkLet :: [(Var, AnfExpr)] -> AnfExpr -> AnfExpr
imm, immExpr :: Expr -> AnfM ([(Var, AnfExpr)], ImmExpr)
anf   :: Expr -> AnfM AnfExpr

-- data IExpr
  -- = IInt Int
  -- | IVar Var
--
-- data AExpr
  -- = AImm IExpr
  -- | ABin Op    IExpr IExpr
  -- | ALet Var   AExpr AExpr
  -- | ALam Var   AExpr
  -- | AApp IExpr IExpr

type AnfExpr = Expr
type ImmExpr = Expr
\end{code}
</div>

Source Language
---------------

Lets commence by defining the source language that we wish to work with:

\begin{code}
data Expr
  = EInt  Int               -- ^ Integers
  | EVar  Var               -- ^ Variables
  | EBin  Op   Expr Expr    -- ^ Binary Operators
  | ELet  Var  Expr Expr    -- ^ Let-binders
  | ELam  Var  Expr         -- ^ Function definitions
  | EApp  Expr Expr         -- ^ Function applications
  deriving (Show)
\end{code}

The language, defined by `Expr` has integers, variables, binary operators,
let-binders and function definitions (lambdas) and calls (applications).
In the above, `Var` and `Op` are simply:

\begin{code}
type Var = String

data Op  = Plus | Minus | Times
         deriving (Show)
\end{code}

For example, the source expression above corresponds to the value:

\begin{code}
-- ((2 + 3) * (12 - 4)) * (7 + 8)
srcExpr :: Expr
srcExpr = EBin Times
            (EBin Times
              (EBin Plus  (EInt  2) (EInt 3))
              (EBin Minus (EInt 12) (EInt 4)))
            (EBin Plus (EInt 7) (EInt 8))
\end{code}

A-Normal Form
-------------

Before we can describe a _conversion_ to A-Normal Form (ANF),
we must pin down what ANF _is_. Our informal description was:
``each call or primitive operation's arguments are immediate
  values, i.e. constants or variable lookups''.

We _could_ define a brand new datatypes, say `IExpr` and `AExpr`
whose values correspond to _immediate_ and _ANF_ terms.
(Try it, as an exercise.) Unfortunately, doing so leads to a
bunch of code duplication, e.g. duplicate printers for `Expr`
and `AExpr`. Instead, lets see how we can use refinements to
carve out suitable subsets.

**Immediate Expressions**

An `Expr` is **immediate** if it is a `Number` or a `Var`;
we can formalize this as a Haskell predicate:

\begin{code}
{-@ measure isImm @-}
isImm :: Expr -> Bool
isImm (EInt _) = True
isImm (EVar _) = True
isImm _        = False
\end{code}

and then we can use the predicate to define a refinement type
for _immediate_ expressions:

\begin{code}
{-@ type ImmExpr = {v:Expr | isImm v} @-}
\end{code}

For example, `e1` is immediate but `e2` is not:

\begin{code}
{-@ e1 :: ImmExpr @-}
e1 = EInt 7

{-@ e2 :: ImmExpr @-}
e2 = EBin Plus e1 e1
\end{code}

**ANF Expressions**

Similiarly, an `Expr` is in **ANF** if all arguments for operators
and applications are **immediate**. Once again, we can formalize
this intuition as a Haskell predicate:

\begin{code}
{-@ measure isAnf @-}
isAnf :: Expr -> Bool
isAnf (EInt {})      = True
isAnf (EVar {})      = True
isAnf (EBin _ e1 e2) = isImm e1 && isImm e2  -- args for operators
isAnf (EApp e1 e2)   = isImm e1 && isImm e2  -- must be immediate,
isAnf (ELet _ e1 e2) = isAnf e1 && isAnf e2  -- and sub-expressions
isAnf (ELam _ e)     = isAnf e               -- must be in ANF
\end{code}

and then use the predicate to define the subset of _legal_ ANF expressions:

\begin{code}
{-@ type AnfExpr = {v:Expr | isAnf v} @-}
\end{code}

For example, `e2` above _is_ in ANF but `e3` is not:

\begin{code}
{-@ e2' :: AnfExpr @-}
e2' = EBin Plus e1 e1

{-@ e3 :: AnfExpr @-}
e3 = EBin Plus e2' e2'
\end{code}

ANF Conversion: Intuition
-------------------------

Now that we have clearly demarcated the territories belonging to plain `Expr`,
immediate `ImmExpr` and A-Normal `AnfExpr`, lets see how we can convert the
former to the latter.

Our goal is to convert expressions like

```haskell
((2 + 3) * (12 - 4)) * (7 + 8)
```

into

```haskell
let anf0 = 2 + 3
    anf1 = 12 - 4
    anf2 = anf0 * anf1
    anf3 = 7 + 8
in
    anf2 * anf3
```

Generalising a bit, we want to convert

```haskell
e1 + e2
```

into

```
let x1  = a1  ... xn  = an
    x1' = a1' ... xm' = am'
in
    v1 + v2
```

where, `v1` and `v2` are immediate, and `ai` are ANF.

**Making Arguments Immediate**

In other words, the key requirement is a way to crunch
arbitrary _argument expressions_ like `e1` into **a pair**

```haskell
([(x1, a1) ... (xn, an)], v1)
```

where

1. `a1...an` are `AnfExpr`, and
2. `v1` is an immediate `ImmExpr`

such that `e1` is _equivalent_ to `let x1 = a1 ... xn = an in v1`.
Thus, we need a function

```haskell
imm :: Expr -> ([(Var, AnfExpr)], ImmExpr)
```

which we will use to **make arguments immediate** thereby yielding
a top level conversion function

```haskell
anf :: Expr -> AnfExpr
```

As we need to generate "temporary" intermediate
binders, it will be convenient to work within a
monad that generates `fresh` variables:

\begin{code}
type AnfM a = State Int a

fresh :: AnfM Var
fresh = do
  n <- get
  put (n+1)
  return ("anf" ++ show n)
\end{code}

Thus, the conversion functions will have the types:

```haskell
anf :: Expr -> AnfM AnfExpr
imm :: Expr -> AnfM ([(Var, AnfExpr)], ImmExpr)
```

ANF Conversion: Code
--------------------

We can now define the top-level conversion thus:

\begin{code}
--------------------------------------------------------------------------------
{-@ anf :: Expr -> AnfM AnfExpr @-}
--------------------------------------------------------------------------------
anf (EInt n) =
  return (EInt n)

anf (EVar x) =
  return (EVar x)

anf (ELet x e1 e2) = do
  a1 <- anf e1
  a2 <- anf e2
  return (ELet x a1 a2)

anf (EBin o e1 e2) = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  return (mkLet (b1s ++ b2s) (EBin o v1 v2))

anf (ELam x e) = do
  a <- anf e
  return (ELam x a)

anf (EApp e1 e2) = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  return (mkLet (b1s ++ b2s) (EApp v1 v2))
\end{code}

In `anf` the real work happens inside `imm` which takes an arbitary
_argument_ expression and makes it **immediate** by generating temporary
(ANF) bindings. The resulting bindings (and immediate values) are
composed by the helper `mkLet` that takes a list of binders and a body
`AnfExpr` and stitches them into a single `AnfExpr`:

\begin{code}
{-@ mkLet :: [(Var, AnfExpr)] -> AnfExpr -> AnfExpr @-}
mkLet []         e' = e'
mkLet ((x,e):bs) e' = ELet x e (mkLet bs e')
\end{code}

The arguments are made immediate by `imm` defined as:

\begin{code}
--------------------------------------------------------------------------------
{-@ imm :: Expr -> AnfM ([(Var, AnfExpr)], ImmExpr) @-}
--------------------------------------------------------------------------------
imm (EInt n)       = return ([], EInt n)
imm (EVar x)       = return ([], EVar x)
imm e@(ELet {})    = immExpr e
imm e@(ELam {})    = immExpr e
imm (EBin o e1 e2) = imm2 e1 e2 (EBin o)
imm (EApp e1 e2)   = imm2 e1 e2 EApp
\end{code}

* Numbers and variables are already immediate, and are returned directly.

* Let-binders and lambdas are simply converted to ANF, and assigned to a fresh
  binder:

\begin{code}
{-@ immExpr :: Expr -> AnfM ([(Var, AnfExpr)], ImmExpr) @-}
immExpr e = do
  a <- anf e
  t <- fresh
  return ([(t, a)], EVar t)
\end{code}

* Finally, binary operators and applications are converted by `imm2` that
  takes two arbitrary expressions and an expression constructor, yielding
  the anf-binders and immediate expression.

\begin{code}
imm2 :: Expr -> Expr -> (ImmExpr -> ImmExpr -> AnfExpr)
     -> AnfM ([(Var, AnfExpr)], ImmExpr)
imm2 e1 e2 f = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  t         <- fresh
  let bs'    = b1s ++ b2s ++ [(t, f v1 v2)]
  return      (bs', EVar t)
\end{code}


You can run it thus:

\begin{code}
toAnf :: Expr -> AnfExpr
toAnf e = evalState (anf e) 0
\end{code}

```haskell
ghci> toAnf srcExpr
ELet "anf0" (EBin Plus (EInt 2) (EInt 3))
 (ELet "anf1" (EBin Minus (EInt 12) (EInt 4))
   (ELet "anf2" (EBin Times (EVar "anf0") (EVar "anf1"))
     (ELet "anf3" (EBin Plus (EInt 7) (EInt 8))
       (EBin Times (EVar "anf2") (EVar "anf3")))))
```

which, can be pretty-printed to yield exactly the outcome desired at the top:

```haskell
let anf0 = 2 + 3
    anf1 = 12 - 4
    anf2 = anf0 * anf1
    anf3 = 7 + 8
in
    anf2 * anf3
```


There! The refinements make this tricky conversion quite
straightforward and natural, without requiring us to
duplicate types and code. As an exercise, can you use
refinements to:

1. Port the classic [continuation-based conversion ?][anf-might]
2. Check that the conversion yields [well-scoped terms ?][lh-scoped]

[lh-scoped]: http://ucsd-progsys.github.io/liquidhaskell-tutorial/10-case-study-associative-maps.html#/using-maps-well-scoped-expressions
[anf-felleisen]: https://users.soe.ucsc.edu/~cormac/papers/pldi93.pdf
[anf-might]: http://matt.might.net/articles/a-normalization/
