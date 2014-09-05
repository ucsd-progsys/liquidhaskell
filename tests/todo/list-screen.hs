{-@ LIQUID "--no-termination" @-}

module ListDemo where

-----------------------------------------------------------------------
-- 1. Lets define a List data-type
-----------------------------------------------------------------------

data List a = E | (:::) { h :: a, t :: List a }

-- We'll want to use the "cons" in an infix fashion

infixr  9 ::: 

-- Ok, now here are some lists

aList :: List Int
aList = 0 ::: 2 ::: 7 ::: E

-- Lets define some simple refinements.

-- | The set of things  that are greater then `N`

{-@ type Geq a N = {v:a | N <= v} @-}

-- | now we can define the *natural* and *positive* numbers as:

{-@ type Nat   = Geq Int 0    @-}
{-@ type Grand = Geq Int 1000 @-}

-- > Lets go back and see if we can refine our lists:

{- up  :: List Grand @-}

-- Whoops, that didn't work of course, how about

{- up  :: List Nat  @-}

-----------------------------------------------------------------------
-- 2. Lets write a function that generates a sequence: n, n+1, n+2, ...
-----------------------------------------------------------------------

{-@ countUp :: n:Nat -> List Nat @-}
countUp n  = n ::: countUp (n + 1)

-- > How shall we type it? Well, one option:

{- countUp :: n:Nat -> List Nat @-}

-- So if you start with a `Nat` you get a list of `Nat`

-- > How about 

{- countUp :: n:Nat -> List Grand @-}

-- Of course not! Lets see the error. Ah, so you can do:

{- countUp :: n:Grand -> List Grand @-}


-----------------------------------------------------------------------
-- 3. ORDERED sequences ...
-----------------------------------------------------------------------

-- Now, really we want to say that `countUp` returns ORDERED sequences,
-- i.e. it returns an INCREASING list of numbers (starting at `n`).

-- Lets specify this by REFINING `List` to only allow INCREASING sequences ...

-- > Lets look at the data type.
-- > Key: INCREASING means `t` must ONLY contain values GREATER THAN head `h`.
                                      
-- that is,

-- t :: List (Geq a h)

-- lets specify that in a REFINED definition of `List`

{-@ data List a = E | (:::) { h :: a, t :: List (Geq a h) } @-}

-- Now lets look at some lists

ups = 0 ::: 1 ::: 3 ::: E 

-- But how about

downs = 7 ::: 2 ::: E

-- > Now lets go back and revisit `countUp` ... whoops there is an ERROR!
-- > This is because we only know the TAIL is a list of Nat, we ALSO need that
-- > the tail is greater than `n` and so ...

{- countUp :: n:Nat -> List (Geq n) @-}


insert x E          = x ::: E
insert x (y ::: ys)
  | x <= y          = x ::: y ::: ys
  | otherwise       = y ::: insert x ys














