
Case Study: Associative Maps
============================

\begin{comment}
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}

module AssocativeMap where

import Data.Set hiding ()

main :: IO ()
main = return ()

{-@ die :: {v:_ | false} -> a @-}
die x   = error x



notMem :: k -> Map k v -> Bool 
set :: (Ord k) => k -> v -> Map k v -> Map k v
get :: (Ord k) => k -> Map k v -> v 
mem :: (Ord k) => k -> Map k v -> Bool


-- | Predicate Aliases
{-@ predicate NoKey M       = Empty (keys M)                        @-}
{-@ predicate HasKey K M    = Set_mem K (keys M)                    @-}
{-@ predicate PlusKey K M N = keys N = Set_cup (Set_sng K) (keys M) @-}
{-@ predicate Subset X Y    = Set_sub X Y                           @-}
{-@ predicate Empty  X      = Set_emp X                             @-}
\end{code}
\end{comment}

\begin{figure}[h]
\includegraphics[height=1.0in]{img/piponi-tweet.png}
\caption{Wouldn't it be nice to know that a key was in a map?} 
\label{fig:piponi-tweet}
\end{figure}

Recall the following from the [introduction](#intro).

\begin{ghci}
ghci> :m +Data.Map 
ghci> let m = fromList [ ("haskell", "lazy")
                       , ("ocaml"  , "eager")]

ghci> m ! "haskell"
"lazy"

ghci> m ! "javascript"
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

Specifying Maps
---------------

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

Using Maps as Environments 
-------------------------- 

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
invented in the first place! Lets define our
environments as `Map`s from `Var`iables to `Val`ues:

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
eval _ i@(Const _)       = i
eval g (Var x)           = get x g 
eval g (Plus e1 e2)      = plus  (eval g e1) (eval g e2) 
eval g (Let x e1 e2)     = eval g' e2 
  where 
    g'                   = set x v1 g 
    v1                   = eval g e1
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
`G` if all the *free* variables in the expression appear in `G`, \ie
the environment contains bindings for all the variables in the
expression that are *not* bound within the expression. As we've seen
repeatedly, often a whole pile of informal handwaving, can be
succinctly captured by a type definition that says the `free` variables
in the `Expr` must be contained in the `keys` of the environment `G`:

\begin{code}
{-@ type ClosedExpr G = {v:Expr | Subset (free v) (keys G)} @-}
\end{code}

\newthought{Closed Evaluation Never Goes Wrong} Now, we can prove that
`eval` will not crash with unbound variables, as long as it is invoked
with suitable environments:

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

**HEREHEREHEREHERE**
**HEREHEREHEREHERE**
**HEREHEREHEREHERE**


Implementing Maps 
-----------------

\newthought{Data Type}

\begin{code}
data Map k v = Node { key   :: k
                    , value :: v
                    , left  :: Map k v
                    , right :: Map k v }
             | Tip 

{-@ data Map k v = Node { key   :: k
                        , value :: v
                        , left  :: Map {v:k | v < key} v
                        , right :: Map {v:k | key < v} v }
                 | Tip 
  @-}
\end{code}

\newthought{Defined Keys}

\begin{code}
{-@ measure keys @-}
keys                :: (Ord k) => Map k v -> Set k
keys Tip            = empty
keys (Node k _ l r) = union (singleton k) (union (keys l) (keys r))
\end{code}

\newthought{Empty Maps}

\begin{code}
{-@ emp :: {m:Map k v | NoKey m} @-}
emp     = Tip 
\end{code}

\newthought{Insert}
\begin{code}

{-@ set :: (Ord k) => k:k -> v -> m:Map k v -> {n: Map k v | PlusKey k m n} @-}
set k' v' (Node k v l r)
  | k' == k   = Node k v' l r
  | k' <  k   = Node k v (set k' v l) r
  | otherwise = Node k v l (set k' v r)
set k' v' Tip = Node k' v' Tip Tip
                
\end{code}

\newthought{Lookup}

\begin{code}
{-@ get :: (Ord k) => k:k -> m:{Map k v | HasKey k m} -> v @-}
get k' (Node k v l r)
  | k' == k   = v

  | k' <  k   = assert (notMem k' r) $
                  get k' l

  | otherwise = assert (notMem k' l)
              $ get k' r
get _ Tip     = die "Lookup failed? Impossible."

{-@ notMem :: key:k -> m:Map {k:k | k /= key} v -> {v:Bool | not (HasKey key m)} @-}
notMem _   Tip            = True 
notMem key (Node _ _ l r) = notMem key l && notMem key r 

assert _ x = x
\end{code}

\newthought{Membership Test}

\begin{code}
{-@ mem :: (Ord k) => k:k -> m:Map k v -> {v:Bool | Prop v <=> HasKey k m} @-}
mem k' (Node k _ l r)
  | k' == k   = True
  | k' <  k   = assert (notMem k' r) $
                  mem k' l
  | otherwise = assert (notMem k' l) $
                  mem k' r
mem _ Tip     = False
\end{code}

