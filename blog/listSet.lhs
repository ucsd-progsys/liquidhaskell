
Whats in a List? Reasoning about Sets of Values 
===============================================

SMT solvers are very expressive. Lets see how we can represent the *set of*
elements in a list, and then write and verify precise specifications about
those sets.

\begin{code}
module ListSets where
\end{code}

First, lets define a "ghost" type that represents sets. 

\begin{code}
data Set a 
\end{code}

We could also just import @Data.Set@ but we choose to define 
it here to make things self-contained.

Next, lets write a measure for the set of elements in a list.
The measure is a simple recursive function that computes the set
by structural recursion on the list.

\begin{code}
{-@ measure elts :: [a] -> (Set a) 
    elts ([])   = {v | (? Set_emp(v))}
    elts (x:xs) = {v | v = (Set_cup (Set_sng x) (elts xs)) }
  @-}
\end{code}

Next, we tell the solver to interpret @Set@ *natively* in the
refinement logic, via the solver's built in sort.

\begin{code}
{-@ embed Set as Set_Set @-}
\end{code}

OK, now we can write some specifications!

A Trivial Identity
------------------

To start with, lets check that the `elts` measure is sensible.

\begin{code}
{-@ myid :: xs:[a] -> {v:[a]| (elts v) = (elts xs)} @-}
myid []     = []
myid (x:xs) = x : myid xs
\end{code}

A Less Trivial Identity
-----------------------

Next, lets write a function @myreverse@ that reverses a list. 
Of course, it should also preserve the set of values thats in 
the list. This is somewhat more interesting because of the 
*tail recursive* helper @go@. Mouse over and see what type 
is inferred for it!

\begin{code}
{-@ myreverse :: xs:[a] -> {v:[a]| (elts v) = (elts xs)} @-}
myreverse = go [] 
  where 
    go acc []     = acc
    go acc (y:ys) = go (y:acc) ys
\end{code}

Appending Lists
---------------

Next, here's good old append, but now with a specification that states
that the output indeed includes the elements from both the input lists.

\begin{code}
{-@ myapp :: xs:[a] -> ys:[a] -> {v:[a] | (elts v) = (Set_cup (elts xs) (elts ys))} @-}
myapp []     ys = ys
myapp (x:xs) ys = x : myapp xs ys
\end{code}

Filtering Lists
---------------

Finally, to round off this little demo, here's @filter@. We can verify
that it returns a subset of the values of the input list.

\begin{code}
{-@ myfilter :: (a -> Bool) -> xs:[a] -> {v:[a]| (? (Set_sub (elts v) (elts xs)))} @-}
myfilter f []     = []
myfilter f (x:xs) 
  | f x           = x : myfilter f xs 
  | otherwise     = myfilter f xs
\end{code}



