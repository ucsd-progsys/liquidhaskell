---
layout: post
title: "Setting Things In Order"
date: 2013-07-29 16:12
comments: true
external-url:
categories: abstract-refinements
author: Niki Vazou and Ranjit Jhala
published: false
---

Abstractly Refined Data
-----------------------

+ Warmup: Dependent Tuples

Abstractly Refined Lists
------------------------

+ Sprint: Abs-Ref-List
+ DEFINE
+ UNROLL

+ EXAMPLE: Types 
  > INCRLIST
  > DECRLIST
  > UNIQLIST

Using Refined Lists
-------------------

+ EXAMPLE: CODE 
  > REVERSE
  > FILTER

Insertion Sort
--------------

+ EXAMPLE 
  > INSERT-SORT

Merge Sort
----------

+ EXAMPLE 
  > MERGE-SORT

Quick Sort
----------

+ EXAMPLE 
  > QUICK-SORT


Well hello again! Much has happened that we're very excited about, and 
which we will get to in the fullness of time. For now, lets continue 
where we [left off][blog-absref] with the saga of *abstract refinements*. 

\begin{code} In a nutshell, this new mechanism allows us to write and check types like:
maxInt :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p>
\end{code}

which states that the output of `maxInt` preserves *whatever* invariants 
held for its two inputs as long as both those inputs *also* satisfied those
invariants. Today, we'll see that this rather innocent looking mechanism 
actually packs quite a punch, by showing how it can *specify* and *verify*
**ordering** properties in recursive data structures.

<!-- more -->

\begin{code}
module ListSort (insertSort, mergeSort, quickSort) where
\end{code}

Abstracting Refinements by Abstracting Types
--------------------------------------------

First, lets see how we can (and why we may want to) 
abstractly refine data types. 

**Polymorphic Association Lists**

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
sparseVecP = [(12 ,  34.1 )
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
{-@ digitsP :: AssocP {v:Int | (0 <= v && v <= 9} String @-}
\end{code}

and 

\begin{code}
{-@ sparseVecP :: AssocP {v:Int | (0 <= v && v <= 1000)} Double @-}
\end{code}

**Monomorphic Association Lists**

Suppose that for one reason or another, how about, say, 
*performance*, we want to specialize our association 
list so that the keys are of type `Int`. 

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
      = KVP [(Int<p>, v)] @-} 
\end{code}

The definition refines the type for `Assoc` to introduce
an abstract refinement `p` which is, informally speaking,
a property of `Int`. The definition states that each `Int`
in the association list in fact satisfies `p` as, `Int<p>`
is an abbreviation for `{v:Int| (p v)}`.

Now, we can *have* our `Int` keys and *refine* them too!
For example, we can write:

\begin{code}
{-@ digits :: Assoc String <{\v -> (0 <= v && v <= 9)}> @-}

{-@ sparseVec :: Assoc Double <{\v -> (0 <= v && v <= 1000)}> @-}
\end{code}

and 

\begin{code}
{-@ sparseVecP :: AssocP {v:Nat | v <= 9} Double @-}
\end{code}

The **keys** used in the two tables have rather different properties: one is a
number between `0` and `9` and the other is between `0` and `999`. 

\begin{code} If the keys were polymorphic, i.e. *if* we had defined the type as
data AssocP k v = KVP [(k, v)]
\end{code}
then we could simply have specified the invariants by appropriately
instantiating `k` with the different refined types, that is:



\begin{code}
sparseVecP :: AssocP Int Double
sparseVecP = [ (12 ,  34.1 )
            , (92 , 902.83)
            , (451,   2.95)
            , (877,   3.1 )]
\end{code}


Suppose we wanted an association list of key-value pairs where the keys were
`Int`egers.

and another table for *sparsely* storing the contents of an array of size `1000`.



Abstractly Refined Lists
------------------------


Let see how we can use **abstract refinements* to verify that
the result of a list sorting function is actually a sorted list.

First, lets describe a sorted list:

\begin{code}The list type is refined with an abstract refinement, yielding the refined type:
data [a] <p :: elt:a -> a -> Bool> where
  | []  :: [a] <p>
  | (:) :: h:a -> [a<p h>]<p> -> [a]<p>
\end{code}

The definition states that a value of type `[a]<p>` is either empty (`[]`)
or constructed from a pair of a head `h::a` and a tail of a list of a values 
each of which satisfies the refinement (`p h`). 
Furthermore, the abstract refinement `p` holds recursively within the
tail, ensuring that the relationship `p` holds between all pairs of list elements.


\begin{code}A sorted list is defined by instantiating the abstract refinement `p` with 
\elt v -> v >= elt
\end{code}

So, we define the type-synonym `SList a`

\begin{code}
{-@ type SList a = [a]<\elt -> {v: a | (v >= elt)}> @-}
\end{code}

We aim to verify that the result of each sorting function is of type `SList a`

Insert Sort
-----------

Lets write a function `insert` that inserts an element into the correct position of a sorted list:

\begin{code}
insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs
\end{code}

Its type states that if you give `insert` an element and a sorted list,
it returns a sorted list.
 
To write `insertSort`, 
we can recursively apply this `insert` to the elements of the list:

\begin{code}
{-@ insertSort :: (Ord a) => xs:[a] -> SList a @-}
insertSort            :: (Ord a) => [a] -> [a]
insertSort []         = []
insertSort (x:xs)     = insert x (insertSort xs) 
\end{code}

And the system can prove that the result of `insertSort` is a sorted list.

Merge Sort
----------

We first write a `merge` function:

\begin{code}
merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
  | x <= y
  = x:(merge xs (y:ys))
  | otherwise 
  = y:(merge (x:xs) ys)
\end{code}

The system can prove that if both arguments of `merge` are sorted lists, 
then its result is also a sorted list.

Next, we write a `split` function that splits any list in two sublists:
\begin{code}
split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])
\end{code}

Finally, using the above functions we write `mergeSort`:

\begin{code}
{-@ mergeSort :: (Ord a) => xs:[a] -> SList a @-}
mergeSort :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort xs1) (mergeSort xs2) where (xs1, xs2) = split xs
\end{code}

The system can prove that the result of `mergeSort` is a sorted list.
For the first two cases empty lists or lists with one element can easily proved
to be sorted. For the last case, if we assume that `mergeSort`'s result is a 
sorted list, then `merge` is applied to two sorted lists, thus its result will
be also a sorted list.

Quick Sort
----------

\begin{code}We would like to define `quickSort` as follows:
quickSort' []     = []
quickSort' (x:xs) = append' lts gts 
  where 
    lts           = quickSort' [y | y <- xs, y < x]
    gts           = quickSort' [z | z <- xs, z >= x]

append' []     ys  = ys
append' (x:xs) ys  = x : append' xs ys
\end{code}


In order for `quicksort` to return a sorted list,
append should return a sorted list.
Thus, we would like to be able to express the fact that `append`
is called with two sorted lists and each element of the first list 
is less than each element of the second.
To do so, we provide `append` one more argument or a "ghost" variable, say `k`, of type `a`
and give it the type

\begin{code}
{-@ append :: k:a -> l:SList {v:a | v<k} -> ge:SList {v:a | v>=k} -> SList a @-}
\end{code}

So, `append` is defined as:

\begin{code}
append :: a -> [a] -> [a] -> [a]
append k []     ys  = ys
append k (x:xs) ys  = x : append k xs ys
\end{code}

And finally we can define `quicksort`:

\begin{code}
{-@ quickSort :: (Ord a) => [a] -> SList a @-}
quickSort []     = []
quickSort (x:xs) = append x lts gts 
  where lts = quickSort [y | y <- xs, y < x]
        gts = quickSort [z | z <- xs, z >= x]
\end{code}


[blog-absref]:     /blog/2013/06/3/abstracting-over-refinements.lhs/
