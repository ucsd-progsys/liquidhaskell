
Case Study: Associative Maps
============================

\begin{comment}
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}

module AssocativeMap where

import Data.Set hiding (elems)
-- | Boilerplate 

{-@ die :: {v:_ | false} -> a @-}
die x   = error x

-- | Haskell Definitions

data Map k v = Node { key   :: k
                    , value :: v
                    , left  :: Map k v
                    , right :: Map k v }
             | Tip 

lemma_notMem :: k -> Map k v -> Bool 
set    :: (Ord k) => k -> v -> Map k v -> Map k v
get    :: (Ord k) => k -> Map k v -> v 
get'   :: (Ord k) => k -> Map k v -> v 
mem    :: (Ord k) => k -> Map k v -> Bool
emp    :: Map k v
elems  :: (Ord a) => [a] -> Set a
fresh  :: [Int] -> Int
-- | Predicate Aliases
{-@ predicate NoKey M       = Empty (keys M)                        @-}
{-@ predicate HasKey K M    = Set_mem K (keys M)                    @-}
{-@ predicate PlusKey K M N = keys N = Set_cup (Set_sng K) (keys M) @-}
{-@ predicate Subset X Y    = Set_sub X Y                           @-}
{-@ predicate Empty  X      = Set_emp X                             @-}
\end{code}
\end{comment}

\begin{comment}
\begin{figure}[h]
\includegraphics[height=1.0in]{img/piponi-tweet.png}
\caption{Wouldn't it be nice to know that a key was in a map?} 
\label{fig:piponi-tweet}
\end{figure}
\end{comment}

Recall the following from the [introduction](#intro).

\begin{ghci}
ghci> :m +Data.Map 
ghci> let m = fromList [ ("haskell"   , "lazy")
                       , ("javascript", "eager")]

ghci> m ! "haskell"
"lazy"

ghci> m ! "python"
"*** Exception: key is not in the map
\end{ghci}

\noindent
The problem illustrated above is quite a pervasive one; associative
maps pop up everywhere. Failed lookups are the equivalent of
`NullPointerDereference` exceptions in languages like Haskell.
It is rather difficult to use Haskell's type system to precisely
characterize the behavior of associative map APIs as ultimately,
this requires tracking the *dynamic set of keys* in the map.

In this case study, we'll see how to combine two techniques -- 
[measures](#setmeasure) for reasoning about the *sets* of elements
in structures, and [refined data types](#refineddatatypes) for
reasoning about order invariants -- can be applied to programs
that use associative maps (e.g. `Data.Map` or `Data.HashMap`).

Specifying Maps {#mapapi}
-------------------------

Lets start by defining a *refined API* for Associative Maps
that tracks the set of keys stored in the map, in order to
statically ensure the safety of lookups.

\newthought{Types} First, we need an (currently abstract)
type for `Map`s. As usual, lets parameterize the type with
`k` for the type of keys and `v` for the type of values.

\begin{spec}
-- | Data Type
data Map k v
\end{spec}

\newthought{Keys} To talk about the set of keys in a map,
we will use a *measure*

\begin{spec}
measure keys :: Map k v -> Set k
\end{spec}

\noindent that associates each `Map` to the `Set` of its
defined keys. Next, we use the above measure, and the usual
`Set` operators to refine the types of the functions that
*create*, *add* and *lookup* key-value bindings, in order
to precisely track, within the type system, the `keys`
that are dynamically defined within each `Map`.

\newthought{Empty} `Map`s have no keys in them. Hence, we
defined a predicate alias, `NoKey` and use it to type `emp`
which is used to denote the empty `Map`:

\begin{spec}
emp :: {m:Map k v | NoKey m}

predicate NoKey M = keys M = Set_empty 0
\end{spec}

\newthought{Add} The function `set` takes a key $k$ a
value $v$ and a map `m` and returns the new map obtained
by extending `m` with the binding ${k \mapsto v}$.
Thus, the set of `keys` of the output `Map` includes
those of the input plus the singleton $k$, that is:

\begin{spec}
set :: (Ord k) => k:k -> v -> m:Map k v -> {n: Map k v | PlusKey k m n}

predicate PlusKey K M N = keys N = Set_cup (Set_sng K) (keys M)
\end{spec}

\newthought{Query} Finally, queries will only succeed for keys that are defined
a given `Map`. Thus, we define an alias:

\begin{spec}
predicate HasKey K M    = Set_mem K (keys M)
\end{spec}

\noindent and use it to type `mem` which *checks* if
a key is defined in the `Map` and `get` which actually
returns the value associated with a given key.

\begin{spec}
-- | Check if key is defined 
mem :: (Ord k) => k:k -> m:Map k v -> {v:Bool | Prop v <=> HasKey k m}

-- | Lookup key's value 
get :: (Ord k) => k:k -> {m:Map k v | HasKey k m} -> v
\end{spec}

Using Maps: Well Scoped Expressions 
----------------------------------- 

Rather than jumping into the *implementation* of the above `Map` API,
lets write a *client* that uses `Map`s to implement an interpreter for
a tiny language. In particular, we will use maps as an *environment*
containing the values of *bound variables*, and we will use the refined
API to ensure that *lookups never fail*, and hence, that well-scoped
programs always reduce to a value.

\newthought{Expressions} Lets work with a simple language with
integer constants, variables, binding and arithmetic operators:
\footnotetext{Feel free to embellish the language with fancier
features like functions, tuples etc.}

\begin{code}
type Var  = String 

data Expr = Const Int
          | Var   Var
          | Plus  Expr Expr
          | Let   Var  Expr Expr
\end{code}

\newthought{Values} We can use refinements to formally
describe *values* as a subset of `Expr` allowing us to
reuse a bunch of code. To this end, we simply define a
(`measure`) predicate characterizing values:

\begin{code}
{-@ measure val @-}
val              :: Expr -> Bool 
val (Const _)    = True 
val (Var _)      = False 
val (Plus _ _)   = False 
val (Let _ _ _ ) = False 
\end{code}

\noindent and then we can use the lifted `measure` to
define an alias for `Val` denoting values:

\begin{code}
{-@ type Val = {v:Expr | val v} @-}
\end{code}

\noindent we can use the above to write simple *operators*
on `Val`, for example:

\begin{code}
{-@ plus                 :: Val -> Val -> Val @-}
plus (Const i) (Const j) = Const (i+j)
plus _         _         = die "Bad call to plus"
\end{code}

\newthought{Environments} let us save values for the
"local" i.e. *let-bound* variables; when evaluating
an expression `Var x` we simply look up the value of
`x` in the environment. This is why `Map`s were
invented! Lets define our environments as `Map`s from `Var`iables to `Val`ues:

\begin{code}
{-@ type Env = Map Var Val @-}
\end{code}

\noindent The above definition essentially specifies, inside the
types, an *eager* evaluation strategy: LiquidHaskell will prevent
us from sticking unevaluated `Expr`s inside the environments.

\newthought{Evaluation} proceeds via a straightforward recursion
over the structure of the expression. When we hit a `Var` we simply
query its value from the environment. When we hit a `Let` we compute
the bound expression and tuck its value into the environment before
proceeding within.

\begin{code}
eval _ i@(Const _)   = i
eval g (Var x)       = get x g 
eval g (Plus e1 e2)  = plus  (eval g e1) (eval g e2) 
eval g (Let x e1 e2) = eval g' e2 
  where 
    g'               = set x v1 g 
    v1               = eval g e1
\end{code}

The above `eval` seems rather unsafe; whats the guarantee that
`get x g` will succeed? For example, surely trying:

\begin{ghci}
ghci> eval emp (Var "x")
\end{ghci}

\noindent will lead to some unpleasant crash. Shouldn't we *check*
if the variables is present and if not, fail with some sort of
`Variable Not Bound` error? We could, but we can do better: we can
prove at compile time, that such errors will not occur.

\newthought{Free Variables} are those whose values are *not* bound
within an expression, that is, the set of variables that *appear* in
the expression, but are not *bound* by a dominating `Let`. We can
formalize this notion as a (lifted) function:

\begin{code}
{-@ measure free @-}
free               :: Expr -> (Set Var) 
free (Const _)     = empty
free (Var x)       = singleton x
free (Plus e1 e2)  = (free e1) `union` (free e2)
free (Let x e1 e2) = (free e1) `union` ((free e2) `difference` (singleton x))
\end{code}

\newthought{An Expression is Closed} with respect to an environment
`G` if all the *free* variables in the expression appear in `G`, i.e.
the environment contains bindings for all the variables in the
expression that are *not* bound within the expression. As we've seen
repeatedly, often a whole pile of informal handwaving, can be
succinctly captured by a type definition that says the `free` variables
in the `Expr` must be contained in the `keys` of the environment `G`:

\begin{code}
{-@ type ClosedExpr G = {v:Expr | Subset (free v) (keys G)} @-}
\end{code}

\newthought{Closed Evaluation} never goes wrong, i.e. we can
ensure that `eval` will not crash with unbound variables, as
long as it is invoked with suitable environments:

\begin{code}
{-@ eval :: g:Env -> ClosedExpr g -> Val @-}
\end{code}

\noindent We can be sure an `Expr` is well-scoped if it has *no*
free variables.Lets use that to write a "top-level" evaluator:

\begin{code}
{-@ topEval :: {v:Expr | Empty (free v)} -> Val @-}
topEval     = eval emp 
\end{code}

\exercise Complete the definition of the below function which
*checks* if an `Expr` is well formed before `eval`uating it:

\begin{code}
{-@ evalAny   :: Env -> Expr -> Maybe Val @-} 
evalAny g e
  | ok        = Just $ eval g e
  | otherwise = Nothing
  where
    ok        = undefined  
\end{code}

\noindent Proof is all well and good, in the end, you need a few
sanity tests to kick the tires. So:

\begin{code}
tests   = [v1, v2]
  where
    v1  = topEval e1          -- Rejected by LH
    v2  = topEval e2          -- Accepted by LH
    e1  = (Var x) `Plus` c1 
    e2  = Let x c10 e1 
    x   = "x"
    c1  = Const 1
    c10 = Const 10
\end{code}

\exercisen{Functions and Closures} \doublestar Extend the language above
to include functions. That is, extend

\begin{spec}
data Expr = ... | Fun Var Expr | App Expr Expr
\end{spec}

Just focus on ensuring the safety of variable lookups;
ensuring full type-safety (i.e. every application is to
a function) is rather more complicated and beyond the
scope of what we've seen so far.


Implementing Maps: Binary Search Trees  
--------------------------------------

We just saw how easy it is to *use* the Associative
Map [API](#mapapi) to ensure the safety of lookups,
even though the `Map` has a "dynamically" generated
set of keys. Next, lets see how we can *implement*
a `Map` library that respects the API using
[Binary Search Trees](#binarysearchtree)

\newthought{Data Type} First, lets provide an
implementation of the (hitherto abstract) data
type for `Map`. We shall use Binary Search Trees,
wherein, at each `Node`, the `left` (resp. `right`)
subtree has keys that are less than (resp. greater than)
the root `key`.

\begin{code}
{-@ data Map k v = Node { key   :: k
                        , value :: v
                        , left  :: Map {v:k | v < key} v
                        , right :: Map {v:k | key < v} v }
                 | Tip 
  @-}
\end{code}

\noindent [Recall](#binarysearchtree) that the above
refined data definition yields strengthened data
constructors that statically ensure that only legal,
*binary-search ordered* trees are created in the program.

\newthought{Defined Keys} Next, we must provide an
implementation of the notion of the `keys` that are
defined for a given `Map`.  This is achieved via the
(lifted) measure function:

\begin{code}
{-@ measure keys @-}
keys                :: (Ord k) => Map k v -> Set k
keys Tip            = empty
keys (Node k _ l r) = union (singleton k) (union (keys l) (keys r))
\end{code}

Armed with the basic type and measure definition, we
can start to fill in the operations for `Maps`.

\exercisen{Empty Maps} To make sure you are following,
fill in the definition for an `emp`ty Map:

\begin{code}
{-@ emp :: {m:Map k v | NoKey m} @-}
emp     = undefined  
\end{code}

\exercisen{Insert} To add a key `k'` to a `Map` we
recursively traverse the `Map` zigging `left` or `right`
depending on the result of comparisons with the keys along
the path. Unfortunately, the version below has an
(all too common!) bug, and hence, is *rejected*
by LiquidHaskell. Find and fix the bug so that
the function is verified.

\begin{code}
{-@ set :: (Ord k) => k:k -> v -> m:Map k v -> {n: Map k v | PlusKey k m n} @-}
set k' v' (Node k v l r)
  | k' == k   = Node k v' l r
  | k' <  k   = set k' v l
  | otherwise = set k' v r
set k' v' Tip = Node k' v' Tip Tip
\end{code}

\newthought{Lookup} Next, lets write the `mem` function that returns
the value associated with a key `k'`. To do so we just compare `k'`
with the root key, if they are equal, we return the binding, and
otherwise we go down the `left` (resp. `right`) subtree if sought for
key is less (resp. greater) than the root `key`. Crucially, we want to
check that lookup *never fails*, and hence, we implement the `Tip`
(i.e. empty) case with `die` gets LiquidHaskell to prove that that
case is indeed dead code, i.e. never happens at run-time.

\begin{code}
{-@ get' :: (Ord k) =>  k:k -> m:{Map k v | HasKey k m} -> v @-}
get' k' m@(Node k v l r)
  | k' == k   = v
  | k' <  k   = get' k' l
  | otherwise = get' k' r
get'  _ Tip   = die  "Lookup Never Fails"
\end{code}

\newthought{Unfortunately} the function above is *rejected*
by LiquidHaskell. This is a puzzler (and a bummer!) because
in fact it *is* correct. So what gives?
Well, lets look at the error for the call `get' k' l`

\begin{liquiderror}
 src/07-case-study-associative-maps.lhs:411:25: Error: Liquid Type Mismatch
   Inferred type
     VV : (Map a b) | VV == l
  
   not a subtype of Required type
     VV : (Map a b) | Set_mem k' (keys VV)

   In Context
     VV : (Map a b) | VV == l
     k  : a
     l  : (Map a b)
     k' : a
\end{liquiderror}

\noindent LiquidHaskell is *unable* to deduce that the the key `k'`
definitely belongs in the `left` subtree `l`. Well, lets ask ourselves:
*why* must `k'` belong in the left subtree? From the input, we know
`HasKey k' m` i.e. that `k'` is *somewhere* in `m`.
That is *one of* the following holds:

1. `k' == k` or,
2. `HasKey k' l` or,
3. `HasKey k' r`.

As the preceding guard `k' == k` fails, we (and LiquidHaskell)
can rule out case (1). Now, what about the `Map` tells us that
case (2) must hold, i.e. that case (3) cannot hold? The *BST invariant*,
all keys in `r` exceed `k` which itself exceeds `k'`. That is,
all nodes in `r` are *disequal* to `k'` and hence `k'` cannot
be in `r`, ruling out case (3). Formally, we need the fact that:
$$\forall\ \vkey,\ \vt. \vt :: {\vMap\ \reft{\vkey'}{k}{\vkey' \not = \vkey}\ v}
                        \ \Rightarrow\
                        \lnot (\vHasKey\ \vkey\ \vt)$$

\newthought{Conversion Lemmas} Unfortunately, LiquidHaskell
*cannot automatically* deduce facts like the above, as they
relate refinements of a container's *type parameters*
(here: $\vkey' \not = \vkey$, which refines the `Map`s first type
parameter) with properties of the entire container
(here: $\vHasKey\ \vkey\ \vt$).
\footnotetext{Why not? This is tricky to describe. Intuitively,
because there is no way of automatically connecting the *traversal*
corresponding to `keys` with the type variable `k`. I wish I had a
better way to explain this rather subtle point; suggestions welcome!}
Fortunately, it is both easy to *state*, *prove* and *use* facts like
the above.

\newthought{Defining Lemmas} To state a lemma, we need only
convert it into a [type](curry-howard) by viewing universal
quantifiers as function parameters, and implications as
function types:

\begin{code}
{-@ lemma_notMem :: key:k -> m:Map {k:k | k /= key} v -> {v:Bool | not (HasKey key m)} @-}
lemma_notMem _   Tip            = True 
lemma_notMem key (Node _ _ l r) = lemma_notMem key l && lemma_notMem key r 
\end{code}

\newthought{Proving Lemmas} Note how the signature for `lemma_notMem`
corresponds exactly to the missing fact from above. The "output" type
is a `Bool` refined with the proposition that we desire. We *prove*
the lemma simply by *traversing* the tree which lets LiquidHaskell
build up a proof for the output fact by inductively combining the
proofs from the subtrees.

\newthought{Using Lemmas} To use a lemma, we need to *instantiate*
it to the particular keys and trees we care about, by "calling" the
lemma function, and forcing its result to be in the *environment* used
to typecheck the expression where we want to use the lemma. Say what?
Here is a verified `get`:

\begin{code}
{-@ get :: (Ord k) => k:k -> m:{Map k v | HasKey k m} -> v @-}
get k' (Node k v l r)
  | k' == k   = v
  | k' <  k   = assert (lemma_notMem k' r) $
                  get k' l
  | otherwise = assert (lemma_notMem k' l) $
                  get k' r
get _ Tip     = die "Lookup failed? Impossible."
\end{code}

By calling `lemma_notMem` we create a dummy `Bool` that carries the desired
refinement that tells LiquidHaskell that `not (HasKey k' r)` (resp. `not (HasKey k' l)`).
We force the calls to `get k' l` (resp. `get k' r`) to be typechecked using
the materialized refinement by wrapping the calls within a function `assert`

\begin{code}
assert _ x = x
\end{code}

\newthought{Ghost Values}
This technique of materializing auxiliary facts via *ghost values* is a
well known idea in the program verification literature. Usually, one has
to take care to ensure that ghost computations do not interfere with the
regular computations. If we had to actually *execute*
`lemma_notMem` it would totally wreck the efficient logarithmic lookup
times \footnotetext{Assuming we kept the trees balanced} as we'd traverse
the entire tree all the time
\footnotetext{Which is what makes dynamic contract checking
[rather slow](findler-contract) for such invariants}

\newthought{Laziness} comes to our rescue: as the ghost value is (trivially)
not needed, it is never computed. In fact, it is straightforward to entirely
*erase* the call in the compiled code, which lets us freely `assert` such
`lemma`s to carry out proofs, without paying any runtime penalty. In an eager
language we would have to do a bit of work to specifically mark the computation
as a ghost or [irrelevant](proof-irrelevance) but in the lazy setting we get
this for free.

\exercisen{Membership Test} Capisce? Fix the definition of `mem` so that
it verifiably implements the given signature:

\begin{code}
{-@ mem :: (Ord k) => k:k -> m:Map k v -> {v:Bool | Prop v <=> HasKey k m} @-}
mem k' (Node k _ l r)
  | k' == k   = True
  | k' <  k   = mem k' l
  | otherwise = mem k' r
mem _ Tip     = False
\end{code}

\exercisen{Fresh} \doublestar To make sure you really understand this business of
ghosts values and proofs, complete the implementation of the following function which
returns a `fresh` integer that is *distinct* from all the values in its input list:

\begin{code}
{-@ fresh :: xs:[Int] -> {v:Int | not (Elem v xs)} @-}
fresh = undefined
\end{code}

\noindent To refresh your memory, here are the definitions for `Elem`
we [saw earlier](#listelems)

\begin{code}
{-@ predicate Elem X Ys  = Set_mem X (elems Ys) @-}
{-@ measure elems @-}
elems []     = empty
elems (x:xs) = (singleton x) `union` (elems xs)
\end{code}

Recap
-----

In this chapter we saw how to combine several of the techniques from previous chapters
in a case study. We learnt how to:

1. **Define** an API for associative maps that used refinements to track the *set* of `keys`
   stored in a map, in order to prevent lookup failures, the `NullPointerDereference` errors
   of the functional world,

2. **Use** the API to implement a small interpreter that is guaranteed to never fail with
   `UnboundVariable` errors, as long as the input expressions were closed,

3. **Implement** the API using Binary Search Trees; in particular, using *ghost lemmas*
   to `assert` facts that LiquidHaskell is otherwise unable to deduce automatically.

