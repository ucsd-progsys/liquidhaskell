% Abstract Refinements

Abstract Refinements
--------------------

\begin{code}
module AbstractRefinements where
\end{code}


Abstract Refinements
--------------------

<br>

\begin{code} Consider the following function 
maxInt     :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 
\end{code}

<br>

\begin{code} We can give `maxInt` many (incomparable) refinement types:
maxInt :: Nat -> Nat -> Nat

maxInt :: Even -> Even -> Even

maxInt :: Prime -> Prime -> Prime
\end{code}

But **which** is the **right** type?


Parametric Invariants 
---------------------

`maxInt` returns *one of* its two inputs `x` and `y`. 

- **If** *both inputs* satisfy a property  

- **Then** *output* must satisfy that property

This holds, **regardless of what that property was!**
 
- That  is, we can **abstract over refinements**

- Or,  **parameterize** a type over its refinements.

Parametric Invariants
--------------------- 

\begin{code}
{-@ maxInt :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p> @-}
maxInt     :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 
\end{code}



Where

- `Int<p>` is just an abbreviation for `{v:Int | (p v)}`


This type states explicitly:

- **For any property** `p`, that is a property of `Int`, 

- `maxInt` takes two **inputs** of which satisfy `p`,

- `maxInt` returns an **output** that satisfies `p`. 


Parametric Invariants via Abstract Refinements
---------------------------------------------- 

\begin{code} We type `maxInt` as
maxInt :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p> 
\end{code}

We call `p` an an **abstract refinement** <br>


In the refinement logic,

- abstract refinements are **uninterpreted function symbols**

- which (only) satisfy the *congruence axiom*: forall x, y. x = y => (p x) = (p y)



Using Abstract Refinements
--------------------------

- **If** we call `maxInt` with two `Int`s with the same concrete refinement,

- **Then** the `p` will be instantiated with that concrete refinement,

- **The output** of the call will also enjoy the concrete refinement.

For example, the refinement is instantiated with `\v -> v >= 0` <br>

\begin{code}
{-@ maxNat :: Nat @-}
maxNat     :: Int
maxNat     = maxInt 2 5
\end{code}

Using Abstract Refinements
--------------------------

- **If** we call `maxInt` with two `Int`s with the same concrete refinement,

- **Then** the `p` will be instantiated with that concrete refinement,

- **The output** of the call will also enjoy the concrete refinement.

Or any other property <br>

\begin{code}
{-@ type RGB = {v: Int | ((0 <= v) && (v < 256)) } @-}
\end{code}

<br> to verify <br>

\begin{code}
{-@ maxRGB :: RGB @-}
maxRGB     :: Int
maxRGB     = maxInt 56 8
\end{code}
