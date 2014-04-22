module Fixme where

import qualified Data.Set 
import Prelude hiding (filter)
data Stack a = Stack { focus  :: !a        -- focused thing in this set
                     , up     :: [a]       -- clowns to the left
                     , down   :: [a] }     -- jokers to the right
    -- deriving (Show, Read, Eq)
data Workspace i l a = Workspace  { tag :: !i, layout :: l, stack :: Maybe (Stack a) }
    -- LIQUID deriving (Show, Read, Eq)
{-@
data Workspace i l a = Workspace  { tag :: i, layout :: l, stack :: Maybe (UStack a) }
  @-}

{-@ stack :: w:(Workspace i l a) 
          -> {v:(Maybe (UStack a)) | v = (getStackWorkspace w)}
  @-}

{-@ measure getStackWorkspace :: (Workspace i l a) -> (Maybe (Stack a))
    getStackWorkspace(Workspace t l stack) = stack @-}
{-@ removeFromWorkspace :: Eq a => a -> Workspace i l a -> Workspace i l a @-}
removeFromWorkspace :: Eq a => a -> Workspace i l a -> Workspace i l a
removeFromWorkspace w ws = ws { stack = stack ws >>= filter (/=w) }

{-@ filter :: (a -> Bool) -> UStack a -> Maybe (UStack a) @-}
filter :: (a -> Bool) -> Stack a -> Maybe (Stack a)
filter = undefined
{-@
data Stack a = Stack { focus :: a   
                     , up    :: UListDif a focus
                     , down  :: UListDif a focus }
@-}

{-@ invariant {v: Stack a | (ListDisjoint (getUp v) (getDown v))}@-}

{-@ measure getUp :: forall a. (Stack a) -> [a] 
    getUp (Stack focus up down) = up
  @-}

{-@ measure getDown :: forall a. (Stack a) -> [a] 
    getDown (Stack focus up down) = down
  @-}

{-@ measure getFocus :: forall a. (Stack a) -> a
    getFocus (Stack focus up down) = focus
  @-}

{-@ qualif Disjoint(v: List a, x:List a) : (Set_emp(Set_cap (listElts v) (listElts x))) @-}

{-@ qualif NoDup(v: List a) : (Set_emp(listDup v)) @-}

{-@ qualif NotMem1(v: List a, x:a) : (not (Set_mem x (listElts v))) @-}

{-@ qualif NotMem2(v:a, x: List a) : (not (Set_mem v (listElts x))) @-}

{-@ qualif NotMem3(v:Stack a) : (Set_emp (Set_cap (listElts (getUp v)) (listElts (getDown v)))) @-}

{-@ type UStack a = {v:(Stack a) | (ListDisjoint (getUp v) (getDown v))}@-}


-- LIQUID HELPERS
{-@ assume (GHC.List.++) :: xs:(UList a)
                -> ys:{v: UList a | (ListDisjoint v xs)}
                -> {v: UList a | (UnionElts v xs ys)}
  @-}
{-@ assume Data.List.filter :: (a -> Bool) 
                            -> xs:(UList a) 
                            -> {v:UList a | (SubElts v xs)} @-}

{-@ assume elem :: Eq a 
                => x:a 
                -> xs:[a] 
                -> {v:Bool|((Prop v)<=>(ListElt x xs))}
  @-}

{-@ assume reverse :: xs:(UList a)
                   -> {v: UList a | (EqElts v xs)} 
  @-}

{-@
  measure listDup :: [a] -> (Data.Set.Set a)
  listDup([])   = {v | (? Set_emp (v))}
  listDup(x:xs) = {v | v = ((Set_mem x (listElts xs))?(Set_cup (Set_sng x) (listDup xs)):(listDup xs)) }
  @-}

{-@ predicate SubElts X Y =
       (Set_sub (listElts X) (listElts Y)) @-}

{-@ predicate UnionElts X Y Z =
       ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}

{-@ predicate EqElts X Y =
       ((listElts X) = (listElts Y)) @-}

{-@ predicate ListUnique LS =
       (Set_emp (listDup LS)) @-}

{-@ predicate ListElt N LS =
       (Set_mem N (listElts LS)) @-}

{-@ predicate ListDisjoint X Y =
       (Set_emp (Set_cap (listElts X) (listElts Y))) @-}

{-@ type UList a = {v:[a] | (ListUnique v)} @-}

{-@ type UListDif a N = {v:[a] | ((not (ListElt N v)) && (ListUnique v))} @-}

