module UniqueZipper where

import Prelude  hiding (reverse, (++), filter)
import Data.Set hiding (filter)

-- | The Set of Values in a List 

-- measure listElts :: [a] -> (Set a)
-- listElts ([])    = {v | (? (Set_emp v))}
-- listElts (x:xs)  = {v | v = (Set_cup (Set_sng x) (listElts xs)) }

{-@ predicate EqElts  X Y      = 
      ((listElts X) = (listElts Y))                        @-}

{-@ predicate DisjointElts X Y = 
      (Set_emp (Set_cap (listElts X) (listElts Y)))        @-}

{-@ predicate SubElts X Y      = 
      (Set_sub (listElts X) (listElts Y))                  @-}

{-@ predicate UnionElts X Y Z  = 
      ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}

{-@ predicate ListElt N X      = 
      (Set_mem N (listElts X))                             @-}

-- | The Set of Unique Values in a List 

{-@
  measure listDup :: [a] -> (Set a)
  listDup([])   = {v | (? (Set_emp v))}
  listDup(x:xs) = {v | v = 
      (if (Set_mem x (listElts xs))
         then (Set_cup (Set_sng x) (listDup xs))
         else (listDup xs)) }
  @-}

{-@ predicate ListUnique X = (Set_emp (listDup X)) @-}

{-@ type UList a = {v:[a] | (ListUnique v)}        @-}


-- | Functions on Unique Lists

infixr 5 ++
{-@ UniqueZipper.++ :: xs:(UList a)
         -> ys:{v: UList a | (DisjointElts v xs)}
         -> {v: UList a | (UnionElts v xs ys)}
  @-}
(++)         :: [a] -> [a] -> [a]
[] ++ ys     = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ reverse :: xs:(UList a)
            -> {v: UList a | (EqElts v xs)} 
  @-}
{-@ Decrease go 2 @-}
reverse :: [a] -> [a]
reverse = go []
  where
    go a []     = a
    go a (x:xs) = go (x:a) xs

{-@ filter :: (a -> Bool) 
           -> xs:(UList a) 
           -> {v:UList a | (SubElts v xs)} 
  @-}
filter      :: (a -> Bool) -> [a] -> [a]
filter p [] = []
filter p (x:xs) 
  | p x       = x : filter p xs
  | otherwise = filter p xs


-- | Unique Zipper

data Zipper a = Zipper { focus :: a       -- focused element in this set
                       , up    :: [a]     -- elements to the left
                       , down  :: [a] }   -- elements to the right

{-@ 
data Zipper a = Zipper { focus :: a
                       , up    :: UListDif a focus
                       , down  :: UListDif a focus }
  @-}

{-@ type UListDif a N = {v:(UList a) | (not (ListElt N v))} @-}

{-@ measure getUp :: forall a. (Zipper a) -> [a]
    getUp (Zipper focus up down) = up
  @-}

{-@ measure getDown :: forall a. (Zipper a) -> [a]
    getDown (Zipper focus up down) = down
  @-}

{-@ 
type UZipper a = {v:Zipper a | (DisjointElts (getUp v) (getDown v))}
  @-}

-- | Functions on Unique Zipper

{-@ differentiate :: UList a -> Maybe (UZipper a) @-}
differentiate :: [a] -> Maybe (Zipper a)
differentiate []     = Nothing
differentiate (x:xs) = Just $ Zipper x [] xs

{-@ integrate :: UZipper a -> UList a @-}
integrate :: Zipper a -> [a]
integrate (Zipper x l r) = reverse l ++ x : r

{-@ reverseZipper :: UZipper a -> UZipper a @-}
reverseZipper :: Zipper a -> Zipper a
reverseZipper (Zipper t ls rs) = Zipper t rs ls

{-@ focusUp, focusDown :: UZipper a -> UZipper a @-}
focusUp, focusDown :: Zipper a -> Zipper a
focusUp (Zipper t [] rs)     = Zipper x xs [] 
  where (x:xs) = reverse (t:rs)
focusUp (Zipper t (l:ls) rs) = Zipper l ls (t:rs)

focusDown = reverseZipper . focusUp . reverseZipper

{-@ q :: x:a ->  {v:[a] |(not (Set_mem x (listElts v)))} @-}
q :: a -> [a]
q _ = []

{-@ filterZipper :: (a -> Bool) -> UZipper a -> Maybe (UZipper a) @-}
filterZipper :: (a -> Bool) -> Zipper a -> Maybe (Zipper a)
filterZipper p (Zipper f ls rs) = case filter p (f:rs) of
    f':rs' -> Just $ Zipper f' (filter p ls) rs'
    []     -> case filter p ls of                  
                    f':ls' -> Just $ Zipper f' ls' []
                    []     -> Nothing
