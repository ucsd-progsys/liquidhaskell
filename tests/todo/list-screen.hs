{-@ LIQUID "--notermination" @-}

module ListDemo where

-----------------------------------------------------------------------
-- 1. Lets define a List data-type
-- 2. Lets force List to have Nat 
-- 3. Lets force List to have Pos
-- 4. Oops, need a different type.
-----------------------------------------------------------------------

data List a = E | (:+:) { h :: a, t :: List a }

-- We'll want to use the "cons" in an infix fashion

infixr  9 :+: 

-- Ok, now here are some lists

nats = 2    :+: 7    :+: 19    :+: E

negs = (-2) :+: (-7) :+: (-19) :+: E


-- Lets define some simple refinements.

-- | The set of `Int` that are greater then `N`

{-@ type Geq N = {v:Int | N <= v } @-}

-- | now we can define the *natural* and *positive* numbers as:

{-@ type Nat   = Geq 0 @-}
{-@ type Pos   = Geq 1 @-}

-- > Lets go back and see if we can refine our lists:

{- up  :: List Pos @-}

-- Whoops, that didn't work of course, how about

{- up  :: List Nat @-}

-----------------------------------------------------------------------
-- Lets write a function that generates a sequence of nats:
-- n, n+1, n+2, ...
-----------------------------------------------------------------------

{- countUp :: n:Nat -> List Nat @-}
countUp n   = n :+: countUp (n + 1)

-- > Of course, we can give it a better type

{-@ countUp :: n:Nat -> List (Geq n) @-}


-- Now, really we want to say that countUp is ORDERED, that is it returns
-- an INCREASING list of numbers (starting at `n`).

-- Lets specify this by REFINING `List` to only allow ORDERED lists...

{-@ data List a = E | (:+:) { h :: a, t :: List {v:a | Geq h} } @-}
                                      
-- the main idea: tail `t` must ONLY contain values that are GREATER THAN the head `h`.
-- that is,
-- t :: List (Geq h)






































countUp :: Int -> List Int


















