module Zipper () where

import Prelude hiding (reverse, (++))

import Data.Set

data Stack a = Stack { focus  :: !a        -- focused thing in this set
                     , up     :: [a]       -- jokers to the left
                     , down   :: [a] }     -- jokers to the right
    deriving (Show, Eq)
-- LIQUID     deriving (Show, Read, Eq)

-------------------------------------------------------------------------------
----------------------------- Refinements on  Lists ---------------------------
-------------------------------------------------------------------------------

-- measures

{-@
  measure listDup :: forall a. [a] -> (Set a)
  listDup([]) = {v | Set_emp v }
  listDup(x:xs) = {v | v = if (Set_mem x (listElts xs)) then (Set_cup (Set_sng x) (listDup xs)) else (listDup xs) }
  @-}

-- predicates 

{-@ predicate EqElts X Y =
       ((listElts X) = (listElts Y)) @-}

{-@ predicate SubElts X Y =
       (Set_sub (listElts X) (listElts Y)) @-}

{-@ predicate UnionElts X Y Z =
       ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}

{-@ predicate ListElt N LS =
       (Set_mem N (listElts LS)) @-}

{-@ predicate ListUnique LS =
       (Set_emp (listDup LS)) @-}

{-@ predicate ListDisjoint X Y =
       (Set_emp (Set_cap (listElts X) (listElts Y))) @-}


-- types

{-@ type UList a = {v:[a] | (ListUnique v)} @-}

{-@ type UListDif a N = {v:[a] | ((not (ListElt N v)) && (ListUnique v))} @-}



-------------------------------------------------------------------------------
----------------------------- Refinements on Stacks ---------------------------
-------------------------------------------------------------------------------

{-@
data Stack a = Stack { focus :: a   
                     , up    :: UListDif a focus
                     , down  :: UListDif a focus }
@-}

{-@ type UStack a = {v:Stack a | (ListDisjoint (getUp v) (getDown v))}@-}

{-@ measure getUp :: forall a. (Stack a) -> [a] 
    getUp (Stack focus up down) = up
  @-}

{-@ measure getDown :: forall a. (Stack a) -> [a] 
    getDown (Stack focus up down) = down
  @-}



-------------------------------------------------------------------------------
------------------------------ Functions on Stacks ----------------------------
-------------------------------------------------------------------------------


{-@ differentiate :: UList a -> Maybe (UStack a) @-}
differentiate :: [a] -> Maybe (Stack a)
differentiate []     = Nothing
differentiate (x:xs) = Just $ Stack x [] xs

{-@ integrate :: UStack a -> UList a @-}
integrate :: Stack a -> [a]
integrate (Stack x l r) = reverse l ++ x : r

{-@ integrate' :: Maybe (UStack a) -> UList a @-}
integrate' :: Maybe (Stack a) -> [a]
integrate' = maybe [] integrate


{-@ focusUp :: UStack a -> UStack a @-}
focusUp :: Stack a -> Stack a
focusUp (Stack t [] rs)     = Stack x xs [] where (x:xs) = reverse (t:rs)
focusUp (Stack t (l:ls) rs) = Stack l ls (t:rs)

{-@ focusDown :: UStack a -> UStack a @-}
focusDown :: Stack a -> Stack a
focusDown = reverseStack . focusUp . reverseStack 

{-@ reverseStack :: UStack a -> UStack a @-}
reverseStack :: Stack a -> Stack a
reverseStack (Stack t ls rs) = Stack t rs ls

{-@ swapUp :: UStack a -> UStack a @-}
swapUp :: Stack a -> Stack a
swapUp  (Stack t (l:ls) rs) = Stack t ls (l:rs)
swapUp  (Stack t []     rs) = Stack t (reverse  rs) []

{-@ filter :: (a -> Bool) -> UStack a -> Maybe (UStack a) @-}
filter :: (a -> Bool) -> Stack a -> Maybe (Stack a)
filter p (Stack f ls rs) = case filterL p (f:rs) of
    f':rs' -> Just $ Stack f' (filterL p ls) rs'    -- maybe move focus down
    []     -> case filterL p ls of                  -- filter back up
                    f':ls' -> Just $ Stack f' ls' [] -- else up
                    []     -> Nothing


-------------------------------------------------------------------------------
------------------------------- Functions on Lists ----------------------------
-------------------------------------------------------------------------------


infixr 5 ++
{-@ Zipper.++ :: xs:(UList a)
         -> ys:{v: UList a | (ListDisjoint v xs)}
         -> {v: UList a | (UnionElts v xs ys)}
  @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x: (xs ++ ys)


{-@ reverse :: xs:(UList a)
            -> {v: UList a | (EqElts v xs)} 
  @-}
reverse :: [a] -> [a]
reverse = rev []


{-@ rev :: ack:(UList a) 
        -> xs:{v: UList a | (ListDisjoint ack v)}
        -> {v:UList a |(UnionElts v xs ack)} 
  @-}
{-@ Decrease rev 2 @-}
rev :: [a] -> [a] -> [a]
rev a []     = a
rev a (x:xs) = rev (x:a) xs 

{-@ filterL :: (a -> Bool) -> xs:(UList a) -> {v:UList a | (SubElts v xs)} @-}
filterL :: (a -> Bool) -> [a] -> [a]
filterL p [] = []
filterL p (x:xs) | p x       = x : filterL p xs
                 | otherwise = filterL p xs


-- QUALIFIERS
{-@ q :: x:a ->  {v:[a] |(not (Set_mem x (listElts v)))} @-}
q :: a -> [a]
q = undefined
