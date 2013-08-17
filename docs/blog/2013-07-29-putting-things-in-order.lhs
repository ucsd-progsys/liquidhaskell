---
layout: post
title: "Putting Things In Order"
date: 2013-07-29 16:12
comments: true
external-url:
categories: abstract-refinements
author: Niki Vazou and Ranjit Jhala
published: true 
demo: Order.hs
---

Hello again! Since we last met, much has happened that
we're rather excited about, and which we promise to get
to in the fullness of time.

Today, however, lets continue with our exploration of
abstract refinements. We'll see that this rather innocent 
looking mechanism packs quite a punch, by showing how 
it can encode various **ordering** properties of 
recursive data structures.

<!-- more -->

\begin{code}
module PuttingThingsInOrder where

import Prelude hiding (break)

-- Haskell Type Definitions
plusOnes                         :: [(Int, Int)]
insertSort, mergeSort, quickSort :: (Ord a) => [a] -> [a]
\end{code}

Abstract Refinements
--------------------

\begin{code} Recall that *abstract refinements* are a mechanism that let us write and check types of the form
maxInt :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p>
\end{code}

which states that the output of `maxInt` preserves 
*whatever* invariants held for its two inputs as 
long as both those inputs *also* satisfied those 
invariants. 

First, lets see how we can (and why we may want to) 
abstractly refine data types. 

Polymorphic Association Lists
-----------------------------

Suppose, we require a type for association lists. 
Lets define one that is polymorphic over keys `k` 
and values `v` 

\begin{code}
data AssocP k v = KVP [(k, v)]
\end{code}

Now, in a program, you might have multiple association
lists, whose keys satisfy different properties. 
For example, we might have a table for mapping digits 
to the corresponding English string

\begin{code}
digitsP :: AssocP Int String
digitsP = KVP [ (1, "one")
              , (2, "two")
              , (3, "three") ]
\end{code}

We could have a separate table for *sparsely* storing 
the contents of an array of size `1000`.

\begin{code}
sparseVecP :: AssocP Int Double
sparseVecP = KVP [ (12 ,  34.1 )
                 , (92 , 902.83)
                 , (451,   2.95)
                 , (877,   3.1 )]
\end{code}

The **keys** used in the two tables have rather 
different properties, which we may want to track 
at compile time.

- In `digitsP` the keys are between `0` and `9` 
- In `sparseVecP` the keys are between `0` and `999`. 

Well, since we had the foresight to parameterize 
the key type in `AssocP`, we can express the above 
properties by appropriately **instantiating** the type
of `k` with refined versions

\begin{code}
{-@ digitsP :: AssocP {v:Int | (Btwn 0 v 9)} String @-}
\end{code}

and 

\begin{code}
{-@ sparseVecP :: AssocP {v:Int | (Btwn 0 v 1000)} Double @-}
\end{code}

where `Btwn` is just an alias 

\begin{code}
{-@ predicate Btwn Lo V Hi = (Lo <= V && V <= Hi) @-}
\end{code}

Monomorphic Association Lists
-----------------------------

Now, suppose that for one reason or another, we want to 
specialize our association list so that the keys are of 
type `Int`. 

\begin{code}
data Assoc v = KV [(Int, v)]
\end{code}

(We'd probably also want to exploit the `Int`-ness 
in the implementation but thats a tale for another day.)

Now, we have our two tables

\begin{code}
digits    :: Assoc String
digits    = KV [ (1, "one")
               , (2, "two")
               , (3, "three") ]

sparseVec :: Assoc Double
sparseVec = KV [ (12 ,  34.1 )
               , (92 , 902.83)
               , (451,   2.95)
               , (877,   3.1 )]
\end{code}

but since we didn't make the key type generic, it seems 
we have no way to distinguish between the invariants of 
the two sets of keys. Bummer!

Abstractly Refined Data
-----------------------

We *could* define *two separate* types of association 
lists that capture different invariants, but frankly, 
thats rather unfortunate, as we'd then have to 
duplicate the code the manipulates the structures. 
Of course, we'd like to have (type) systems help 
keep an eye on different invariants, but we'd 
*really* rather not have to duplicate code to 
achieve that end. Thats the sort of thing that
drives a person to JavaScript ;-).

Fortunately, all is not lost. 

If you were paying attention [last time][blog-absref] 
then you'd realize that this is the perfect job for 
an abstract refinement, this time applied to a `data` 
definition:

\begin{code}
{-@ data Assoc v <p :: Int -> Prop> 
      = KV (z :: [(Int<p>, v)]) @-} 
\end{code}

The definition refines the type for `Assoc` to introduce
an abstract refinement `p` which is, informally speaking,
a property of `Int`. The definition states that each `Int`
in the association list in fact satisfies `p` as, `Int<p>`
is an abbreviation for `{v:Int| (p v)}`.

Now, we can *have* our `Int` keys and *refine* them too!
For example, we can write:

\begin{code}
{-@ digits :: Assoc (String) <{\v -> (Btwn 0 v 9)}> @-}
\end{code}

to track the invariant for the `digits` map, and write

\begin{code}
{-@ sparseVec :: Assoc Double <{\v -> (Btwn 0 v 1000)}> @-}
\end{code}

Thus, we can recover (some of) the benefits of abstracting 
over the type of the key by instead parameterizing the type
directly over the possible invariants. We will have much 
[more to say][blog-absref-vec] on association lists 
(or more generally, finite maps) and abstract refinements, 
but lets move on for the moment.

Dependent Tuples
----------------

It is no accident that we have reused Haskell's function 
type syntax to define abstract refinements (`p :: Int -> Prop`);
interesting things start to happen if we use multiple parameters.

Consider the function `break` from the Prelude. 

\begin{code}
break                   :: (a -> Bool) -> [a] -> ([a], [a])
break _ xs@[]           =  (xs, xs)
break p xs@(x:xs')
           | p x        =  ([], xs)
           | otherwise  =  let (ys, zs) = break p xs' 
                           in (x:ys,zs)
\end{code}

From the comments in [Data.List][data-list], `break p xs`: 
"returns a tuple where the first element is longest prefix (possibly empty)
`xs` of elements that do not satisfy `p` and second element is the 
remainder of the list."

We could formalize the notion of the *second-element-being-the-remainder* 
using sizes. That is, we'd like to specify that the length of the second 
element equals the length of `xs` minus the length of the first element.  
That is, we need a way to allow the refinement of the second element to 
*depend on* the value in the first refinement.
Again, we could define a special kind of tuple-of-lists-type that 
has the above property *baked in*, but thats just not how we roll.

\begin{code} Instead, lets use abstract refinements to give us **dependent tuples**
data (a,b)<p :: a -> b -> Prop> = (x:a, b<p x>) 
\end{code}

Here, the abstract refinement takes two parameters, 
an `a` and a `b`. In the body of the tuple, the 
first element is named `x` and we specify that 
the second element satisfies the refinement `p x`, 
i.e. a partial application of `p` with the first element. 
In other words, the second element is a value of type
`{v:b | (p x v)}`.

As before, we can instantiate the `p` in *different* ways. 
For example the whimsical

\begin{code}
{-@ plusOnes :: [(Int, Int)<{\x1 x2 -> x2 = x1 + 1}>] @-}
plusOnes = [(0,1), (5,6), (999,1000)]
\end{code}

and returning to the *remainder* property for  `break` 

\begin{code}
{-@ break :: (a -> Bool) -> x:[a] 
          -> ([a], [a])<{\y z -> (Break x y z)}> @-}
\end{code}

using the predicate alias

\begin{code}
{-@ predicate Break X Y Z   = (len X) = (len Y) + (len Z) @-}
\end{code}


Abstractly Refined Lists
------------------------

Right, we've been going on for a bit. Time to put things *in order*.

To recap: we've already seen one way to abstractly refine lists: 
to recover a *generic* means of refining a *monomorphic* list 
(e.g. the list of `Int` keys.) However, in that case we were 
talking about *individual* keys.
Next, we build upon the dependent-tuples technique we just 
saw to use abstract refinements to relate *different* 
elements inside containers.

In particular, we can use them to specify that *every pair* 
of elements inside the list is related according to some 
abstract relation `p`. By *instantiating* `p` appropriately,
we will be able to recover various forms of (dis) order. 

\begin{code} Consider the refined definition of good old Haskell lists:
data [a] <p :: a -> a -> Prop> where
  | []  :: [a] <p>
  | (:) :: h:a -> [a<p h>]<p> -> [a]<p>
\end{code}

Whoa! Thats a bit of a mouthful. Lets break it down.

* The type is parameterized with a refinement `p :: a -> a -> Prop` 
  Think of `p` as a *binary relation* over the `a` values comprising
  the list.

* The empty list `[]` is a `[]<p>`. Clearly, the empty list has no
  elements whatsoever and so every pair is trivially, or rather, 
  vacuously related by `p`.

* The cons constructor `(:)` takes a head `h` of type `a` and a tail
  of `a<p h>` values, each of which is *related to* `h` **and** which 
  (recursively) are pairwise related `[...]<p>` and returns a list where 
  *all* elements are pairwise related `[a]<p>`.

Pairwise Related
----------------

Note that we're being a bit sloppy when we say *pairwise* related.

\begin{code} What we really mean is that if a list
[x1,...,xn] :: [a]<p>
\end{code}

then for each `1 <= i < j <= n` we have `(p xi xj)`.

\begin{code} To see why, consider the list
[x1, x2, x3, ...] :: [a]<p>
\end{code}

\begin{code} This list unfolds into a head and tail 
x1                :: a
[x2, x3,...]      :: [a<p x1>]<p>
\end{code}

\begin{code} The above tail unfolds into
x2                :: a<p x1>
[x3, ...]         :: [a<p x1 && p x2>]<p>
\end{code}

\begin{code} And finally into 
x3                :: a<p x1 && p x2>
[...]             :: [a<p x1 && p x2 && p x3>]<p>
\end{code}

That is, each element `xj` satisfies the refinement 
`(p xi xj)` for each `i < j`.

Using Abstractly Refined Lists
------------------------------

Urgh. *Math is hard!*  

Lets see how we can *program* with these funnily refined lists.

For starters, we can define a few helpful type aliases.

\begin{code}
{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}      
{-@ type DecrList a = [a]<{\xi xj -> xi >= xj}> @-}
{-@ type UniqList a = [a]<{\xi xj -> xi /= xj}> @-}
\end{code}

As you might expect, an `IncrList` is a list of values in *increasing* order:

\begin{code}
{-@ whatGosUp :: IncrList Integer @-}
whatGosUp = [1,2,3]
\end{code}

Similarly, a `DecrList` contains its values in *decreasing* order:

\begin{code}
{-@ mustGoDown :: DecrList Integer @-}
mustGoDown = [3,2,1]
\end{code}

My personal favorite though, is a `UniqList` which has *no duplicates*:

\begin{code}
{-@ noDuplicates :: UniqList Integer @-}
noDuplicates = [1,3,2]
\end{code}

Sorting Lists
-------------

Its all very well to *specify* lists with various kinds of invariants. 
The question is, how easy is it to *establish* these invariants?

Lets find out, by turning inevitably to that staple of all forms of
formal verification: your usual textbook sorting procedures.

**Insertion Sort**

First up: insertion sort. Well, no surprises here:

\begin{code}
{-@ insertSort    :: (Ord a) => xs:[a] -> (IncrList a) @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs) 
\end{code}

The hard work is done by `insert` which places an 
element into the correct position of a sorted list

\begin{code}
insert y []     = [y]
insert y (x:xs) 
  | y <= x      = y : x : xs 
  | otherwise   = x : insert y xs
\end{code}

LiquidHaskell infers that if you give `insert` an element 
and a sorted list, it returns a sorted list.

\begin{code}
{-@ insert :: (Ord a) => a -> IncrList a -> IncrList a @-}
\end{code}

If you prefer the more Haskelly way of writing insertion sort, 
i.e. with a `foldr`, that works too. Can you figure out why?

\begin{code}
{-@ insertSort' :: (Ord a) => [a] -> IncrList a @-}
insertSort' xs  = foldr insert [] xs
\end{code}

**Merge Sort**

Well, you know the song goes. First, we write a function 
that **splits** the input into two parts:

\begin{code}
split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys) 
  where 
    (xs, ys)   = split zs
split xs       = (xs, [])
\end{code}

Then we need a function that **merges** two (sorted) lists

\begin{code}
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys) 
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys
\end{code}

LiquidHaskell deduces that if both inputs are 
ordered, then so is the output.

\begin{code}
{-@ merge :: (Ord a) => IncrList a 
                     -> IncrList a 
                     -> IncrList a 
  @-}
\end{code}

Finally, using the above functions we write `mergeSort`:

\begin{code}
{-@ mergeSort :: (Ord a) => [a] -> IncrList a @-}
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs) 
  where 
    (ys, zs)  = split xs
\end{code}

Lets see how LiquidHaskell proves the output type. 

+ The first two cases are trivial: for an empty 
  or singleton list, we can vacuously instantiate 
  the abstract refinement with *any* concrete 
  refinement.

+ For the last case, we can inductively assume 
 `mergeSort ys` and `mergeSort zs` are sorted 
  lists, after which the type inferred for 
  `merge` kicks in, allowing LiquidHaskell to conclude
  that the output is also sorted.

**Quick Sort**

The previous two were remarkable because they were, well, quite *unremarkable*. 
Pretty much the standard textbook implementations work *as is*. 
Unlike the [classical][omega-sort] [developments][hasochism] 
using indexed types we don't have to define any auxiliary 
types for increasing lists, or lists whose value is in a 
particular range, or any specialized `cons` operators and 
so on.

With *quick sort* we need to do a tiny bit of work.


\begin{code} We would like to define `quickSort` as
{-@ quickSort'    :: (Ord a) => [a] -> IncrList a @-}
quickSort' []     = []
quickSort' (x:xs) = lts ++ (x : gts) 
  where 
    lts           = quickSort' [y | y <- xs, y < x]
    gts           = quickSort' [z | z <- xs, z >= x]
\end{code}

But, if you try it out, you'll see that LiquidHaskell 
*does not approve*. What could possibly be the trouble?

The problem lies with *append*. What type do we give `++`? 

\begin{code} We might try something like
(++) :: IncrList a -> IncrList a -> IncrList a
\end{code}

\begin{code} but of course, this is bogus, as 
[1,2,4] ++ [3,5,6]
\end{code}

is decidedly not an `IncrList`!

Instead, at this particular use of `++`, there is
an extra nugget of information: there is a *pivot*
element `x` such that every element in the first 
argument is less than `x` and every element in 
the second argument is greater than `x`. 

There is no way we can give the usual append `++` 
a type that reflects the above as there is no pivot 
`x` to refer to. Thus, with a heavy heart, we must
write a specialized pivot-append that uses this fact:

\begin{code}
pivApp piv []     ys  = piv : ys
pivApp piv (x:xs) ys  = x   : pivApp piv xs ys
\end{code}

Now, LiquidHaskell infers that 

\begin{code}
{-@ pivApp :: piv:a 
           -> IncrList {v:a | v <  piv} 
           -> IncrList {v:a | v >= piv} 
           -> IncrList a 
  @-}
\end{code}

And we can use `pivApp` to define `quickSort' simply as:

\begin{code}
{-@ quickSort    :: (Ord a) => [a] -> IncrList a @-}
quickSort []     = []
quickSort (x:xs) = pivApp x lts gts 
  where 
    lts          = quickSort [y | y <- xs, y < x ]
    gts          = quickSort [z | z <- xs, z >= x]
\end{code}

Really Sorting Lists
--------------------

The convenient thing about our encoding is that the 
underlying datatype is plain Haskell lists. 
This yields two very concrete benefits. 
First, as mentioned before, we can manipulate 
sorted lists with the same functions we'd use 
for regular lists.
Second, by decoupling (or rather, parameterizing)
the relation or property or invariant from the actual 
data structure we can plug in different invariants, 
sometimes in the *same* program.

To see why this is useful, lets look at a *real-world* 
sorting algorithm: the one used inside GHC's 
`Data.List` [module][data-list].

\begin{code}
sort :: (Ord a) => [a] -> [a]
sort = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `compare` b == GT = descending b [a]  xs
      | otherwise           = ascending  b (a:) xs
    sequences [x] = [[x]]
    sequences []  = [[]]

    descending a as (b:bs)
      | a `compare` b == GT = descending b (a:as) bs
    descending a as bs      = (a:as): sequences bs

    ascending a as (b:bs)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs       = as [a]: sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs [x]      = [x]
    mergePairs []       = []
\end{code}

The interesting thing about the procedure is that it 
generates some intermediate lists that are increasing 
*and* others that are decreasing, and then somehow
miraculously whips this whirlygig into a single 
increasing list.

Yet, to check this rather tricky algorithm with 
LiquidHaskell we need merely write:

\begin{code}
{-@ sort :: (Ord a) => [a] -> IncrList a  @-}
\end{code}



[blog-absref]:     /blog/2013/06/3/abstracting-over-refinements.lhs/
[blog-absref-vec]: http://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf
[data-list]:        http://www.haskell.org/ghc/docs/latest/html/libraries/base/src/Data-List.html#sort
[omega-sort]:      http://web.cecs.pdx.edu/~sheard/Code/InsertMergeSort.html
[hasochism]:       https://personal.cis.strath.ac.uk/conor.mcbride/pub/hasochism.pdf

