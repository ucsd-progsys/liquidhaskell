{-@ LIQUID "--no-totality" @-}

module Zipper0 (getUp, getDown, getFocus) where

import Prelude hiding (reverse)

import Data.Set

data Stack a = Stack { focus  :: !a        -- focused thing in this set
                     , up     :: [a]       -- jokers to the left
                     , down   :: [a] }     -- jokers to the right

{-@ type UListDif a N = {v:[a] | ((not (Set_mem N (listElts v))) && (Set_emp (listDup v)))} @-}

{-@
data Stack a = Stack { focus :: a
                     , up    :: UListDif a focus
                     , down  :: UListDif a focus }
@-}

{-@ measure listDup :: [a] -> (Set a)
      listDup [] = {v | Set_emp v }
      listDup (x:xs) = {v | v = if (Set_mem x (listElts xs)) then (Set_cup (Set_sng x) (listDup xs)) else (listDup xs) }
  @-}

{-@ type UStack a = {v:Stack a |(Set_emp (Set_cap (listElts (getUp v)) (listElts (getDown v))))}@-}

{-@ measure getFocus @-}
getFocus :: Stack a -> a
getFocus (Stack xfocus _ _) = xfocus

{-@ measure getUp @-}
getUp :: Stack a -> [a]
getUp (Stack xfocus xup xdown) = xup

{-@ measure getDown @-}
getDown :: Stack a -> [a]
getDown (Stack xfocus xup xdown) = xdown


-- QUALIFIERS
{-@ q :: x:a ->  {v:[a] |(not (Set_mem x (listElts v)))} @-}
q :: a -> [a]
q = undefined
{-@ q1 :: x:a ->  {v:[a] |(Set_mem x (listElts v))} @-}
q1 :: a -> [a]
q1 = undefined
{-@ q0 :: x:a ->  {v:[a] |(Set_emp(listDup v))} @-}
q0 :: a -> [a]
q0 = undefined


{-@ focusUp :: UStack a -> UStack a @-}
focusUp :: Stack a -> Stack a
focusUp (Stack t [] rs)     = Stack xiggety xs [] where (xiggety:xs) = reverse (t:rs)
focusUp (Stack t (l:ls) rs) = Stack l ls (t:rs)

{-@ focusDown :: UStack a -> UStack a @-}
focusDown :: Stack a -> Stack a
focusDown = reverseStack . focusUp . reverseStack

-- | reverse a stack: up becomes down and down becomes up.
{-@ reverseStack :: UStack a -> UStack a @-}
reverseStack :: Stack a -> Stack a
reverseStack (Stack t ls rs) = Stack t rs ls


-- TODO ASSUMES
{-@ reverse :: {v:[a] | (Set_emp (listDup v))} -> {v:[a]|(Set_emp (listDup v))} @-}
reverse :: [a] -> [a]
reverse = undefined
