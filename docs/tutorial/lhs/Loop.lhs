% Higher Order Specifications


Higher Order Specifications
---------------------------

\begin{code}
module Loop where

{-@ LIQUID "--no-termination"@-}
\end{code}


Higher Order Specifications
---------------------------

Consider a `loop` function: <br>

\begin{code}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f        = go lo base
  where 
    go i acc | i < hi    = go (i+1) (f i acc)
             | otherwise = acc
\end{code}

<br>

LiquidHaskell **infers**

- if `lo <= hi` then `f` called with `lo <= i < hi`


Higher Order Specifications
---------------------------

Lets use `(!!)` to write a function that sums an `Int` list

\begin{code}
{-@ listSum :: [Int] -> Int @-}
listSum     :: [Int] -> Int
listSum xs  = loop 0 n 0 body 
  where 
    body    = \i acc -> acc + (xs !! i)
    n       = length xs
\end{code}

By **function subtyping** LiquidHaskell **infers**

- `body` called with `0 <= i < llen xs` 
- hence, indexing safe.

<a href="http://goto.ucsd.edu:8090/index.html#?demo=Loop.hs" target= "_blank">Demo:</a> 
Let's change the `0` to `-1` and see what happens!

Higher Order Specifications
---------------------------

We can give this function a better type:

\begin{code}
{-@ listNatSum :: [Nat] -> Nat @-}
listNatSum     :: [Int] -> Int
listNatSum xs  = loop 0 n 0 body 
  where 
    body       = \i acc -> acc + (xs !! i)
    n          = length xs
\end{code}

To verify this type, note: `(+) :: Nat -> Nat -> Nat` 

LiquidHaskell **instantiates** `a` in `loop` with `Nat` 

- `loop :: Int -> Int -> Nat -> (Int -> Nat -> Nat) -> Nat`

Yielding the output.

Higher Order Specifications
---------------------------

By the same analysis, LiquidHaskell verifies that <br>

\begin{code}
{-@ listEvenSum :: [Even] -> Even @-}
listEvenSum     :: [Int] -> Int
listEvenSum xs  = loop 0 n 0 body 
  where body   = \i acc -> acc + (xs !! i)
        n      = length xs
\end{code}

Here, the system deduces that `(+)` has type

- `x:Int-> y:Int -> {v:Int| v=x+y} <: Even -> Even -> Even`

Hence, verification proceeds by *instantiating* `a` with `Even`

- `loop :: Int -> Int -> Even -> (Int -> Even -> Even) -> Even`



Another Example
---------------

Consider a simpler example:<br>

\begin{code}
{-@ add :: n:Nat -> m:Nat -> {v:Int| v = m + n} @-}
add     :: Int -> Int -> Int
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}

Cannot use parametric polymorphism as before! 

- Cannot instantiate `a` with `{v:Int|v = n + m}` ... 
- ... as this only holds after **last iteration** of loop!

Require Higher Order Invariants

- On values computed in **intermediate** iterations...
- ... i.e. invariants that **depend on the iteration index**.

