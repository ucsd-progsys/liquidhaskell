
Inductive Refinements
---------------------

\begin{code}
module Loop where
import Prelude hiding ((!!), foldr, length, (++))
-- import Measures
import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--no-termination" @-}

data L a = N 
         | C a (L a)

{-@ measure llen  :: (L a) -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)  @-}

\end{code}


`loop` Revisited
----------------

Recall the **higher-order** `loop` function <br>

\begin{code}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f            = go lo base
  where go i acc | i < hi    = go (i+1) (f i acc)
                 | otherwise = acc
\end{code}

We used `loop` to write <br>

\begin{code}

{-@ add :: n:Nat -> m:{v:Int| v >= 0} -> {v:Int| v = m + n} @-}
add :: Int -> Int -> Int
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}

**Problem:** Verification requires an **index dependent loop invariant** `p` 

- Which relates index `i` with accumulator `acc`: formally `(p acc i)`

Loop Invariants and Induction
-----------------------------
\begin{code} Recall the **higher-order** `loop` function
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f            = go lo base
  where go i acc | i < hi    = go (i+1) (f i acc)
                 | otherwise = acc
\end{code}

To verify output satisfies relation at `hi` we prove that **if**

- **base case** initial accumulator `base` satisfies invariant at `lo`
    - `(p base lo)`

- **induction step** `f` **preserves** the invariant at `i`
    - **if** `(p acc i)` <b>then</b> `(p (f i acc) (i+1))`

- **then** "by induction" result satisfies invariant at `hi`
    - `(p (loop lo hi base f) hi)`


Encoding Induction With Abstract Refinements
--------------------------------------------

We capture induction with an **abstract refinement type** for `loop` <br>

\begin{code}
{-@ loop :: forall a <p :: Int -> a -> Prop>.
             lo:Int 
          -> hi:{v:Int|lo <= v}
          -> base:a<p lo> 
          -> f:(i:Int -> a<p i> -> a<p (i+1)>) 
          -> a<p hi>
  @-}
\end{code}

<br>

\begin{code} `p` is the index dependent invariant!
p     :: Int -> a -> Prop>                  -- ind  hyp 
base  :: a<p lo>                            -- base case 
f     :: (i:Int -> a<p i> -> a <p (i+1)>)   -- ind. step
out   :: a<p hi>                            -- output holds at hi         
\end{code}


Encoding Induction With Abstract Refinements
--------------------------------------------

\begin{code} Lets revisit 
add n m = loop 0 m n (\_ z -> z + 1)
\end{code}

<br> The invariant is: `p` instantiated with `\i acc -> acc = i + n`

**base case:**  `(p 0 n)` holds as `n = 0 + n`

**ind. step**  `\_ z -> z + 1` preserves invariant

- `acc =  i + n` *implies* `acc + 1 = (i + 1) + n`

**output** hence, `loop 0 m n (\_ z -> z + 1) = m + n`

Which lets us verify that

\begin{code}.
add :: n:Nat -> m:Nat -> {v:Int| v = m + n}
\end{code}

Structural Induction With Abstract Refinements
----------------------------------------------

Same idea applies for induction over *structures*

We define a `foldr` function that resembles loop.
\begin{code}
\end{code}
\begin{code}
{-@ foldr :: forall a b <p :: L a -> b -> Prop>. 
                (xs:L a -> x:a -> b <p xs> -> b <p (C x xs)>) 
              -> b <p N> 
              -> ys: L a
              -> b <p ys>
  @-}
foldr :: (L a -> a -> b -> b) -> b -> L a -> b
foldr f b N        = b
foldr f b (C x xs) = f xs x (foldr f b xs)
\end{code}

<br>

- **base case** `b` is related to nil `N`
- **ind. step** `f` extends relation over cons `C`
- **output** relation holds over entire list `ys`



Structural Induction With Abstract Refinements
----------------------------------------------

We can now verify <br>

\begin{code}
{-@ size :: xs:L a -> {v: Int | v = (llen xs)} @-}
size :: L a -> Int
size = foldr (\_ _ n -> n + 1) 0
\end{code}

<br>

Here, the relation 

- `(p xs acc)` 

is **automatically instantiated** with

- `acc = (llen xs)`

Structural Induction With Abstract Refinements
----------------------------------------------

Similarly we can now verify <br>

\begin{code}_
{-@ ++ :: xs:L a -> ys:L a -> {v:L a | (llen v) = (llen xs) + (llen ys)} @-} 
xs ++ ys = foldr (\_ z zs -> C z zs) ys xs 
\end{code}

<br>

Here, the relation 

- `(p xs acc)` 

is **automatically instantiated** with

- `(llen acc) = (llen xs) + (llen ys)`


