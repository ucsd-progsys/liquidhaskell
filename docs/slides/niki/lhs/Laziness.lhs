% Laziness

Laziness
--------


\begin{code}
module Laziness where
import Language.Haskell.Liquid.Prelude
\end{code}


Infinite Computations can lead to Unsoundness
----------------------------------------------

Infinite Computations can be refined with **false**
\begin{code}
{-@ foo :: n:Nat -> {v:Nat | v < n} @-}
foo     :: Int -> Int
foo n   | n > 0     = n - 1
        | otherwise = foo n
\end{code}

<br>

Under **false** anything can be proven
\begin{code}
prop = liquidAssert ((\x -> 0==1) (foo 0))
\end{code}

<a href="http://goto.ucsd.edu:8090/index.html#?demo=TellingLies.hs" target=
"_blank">Demo:</a> Check a real property here! 

Our solution (Current Work)
---------------------------

- Use **termination analysis** to track infinite computations

- Use **true** refinements for infinite computations


Size-based Termination Analysis
-------------------------------

- Use refinement types to force the recursive argument to **decrease**
\begin{code}
{-@ unsafeFoo :: n:Nat -> {v:Nat | v < n} @-}
unsafeFoo     :: Int -> Int
  -- unsafeFoo :: n'{v:Nat | v < n} -> {v:Nat | v < n'}
unsafeFoo n   | n > 0     = n - 1
              | otherwise = unsafeFoo n
\end{code}

<br>

- `prop` is safe, but the program is decided unsafe
\begin{code}
prop1 = liquidAssert ((\x -> 0==1) inf)
  where inf = unsafeFoo 0
\end{code}

Refinements of infinite Computations
------------------------------------
If you need a non-terminating function, use `Lazy` to declare

 - We know that `foo` may not terminate

 - Its return type is refined with **true**

\begin{code}
{-@ Lazy safeFoo @-}
{-@ safeFoo :: n:Nat -> {v:Int | true} @-}
safeFoo    :: Int   -> Int
safeFoo n   | n > 0     = n - 1
            | otherwise = safeFoo n
\end{code}

<br>

Now, `prop` is unsafe

\begin{code}
prop2 = liquidAssert ((\x -> 0==1) inf)
  where inf = safeFoo 0
\end{code}

Restore Soundness
-----------------

- Use **termination analysis** to track infinite objects

- Use **true** refinements for infinite objects

`Foo` was declared `Lazy`
-------------------------
\begin{code}
{-@ Lazy foo @-}
\end{code}

