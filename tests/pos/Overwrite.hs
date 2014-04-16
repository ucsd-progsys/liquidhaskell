module OverWrite where

import qualified Data.Set

{-@ assume reverse :: xs:(UList a)
                   -> {v: UList a | (EqElts v xs)} 
  @-}
{-@ type UList a = {v:[a] | (ListUnique v)} @-}

{-@ predicate ListUnique LS =
       (Set_emp (listDup LS)) @-}

{-@ predicate EqElts X Y =
       ((listElts X) = (listElts Y)) @-}
{-@
  measure listDup :: [a] -> (Data.Set.Set a)
  listDup([])   = {v | (? Set_emp (v))}
  listDup(x:xs) = {v | v = ((Set_mem x (listElts xs))?(Set_cup (Set_sng x) (listDup xs)):(listDup xs)) }
  @-}

{-@ foo :: xs:(UList a)
        -> {v: UList a | (EqElts v xs)} 
  @-}


foo  = reverse 
