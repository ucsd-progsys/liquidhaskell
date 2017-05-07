module Range () where

{-@ data LL [llen] @-} 
data LL a = N | C a (LL a)

-- ISSUE: LH should give a proper error message if there is 
-- an "unlifted" measure that has the same name as a code 
-- function.

{-@ invariant {v:LL a | (llen v) >= 0} @-}

{-@ measure llen :: (LL a) -> Int 
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}


llen :: (LL a) -> Int 
llen(N)      = 0
llen(C x xs) = 1 + (llen xs)

lmap f N = N
lmap f (C x xs) = C (f x) (lmap f xs)

