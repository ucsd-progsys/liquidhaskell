{-@ LIQUID "--no-totality" @-}

module Zipper (getUp, getDown) where

import Data.Set

data Stack a = Stack { focus  :: !a        -- focused thing in this set
                     , up     :: [a]       -- jokers to the left
                     , down   :: [a] }     -- jokers to the right

{-@ type UListDif a N = {v:[a] | not (Set_mem N (listElts v)) } @-}

{-@
data Stack a = Stack { focus :: a
                     , up    :: UListDif a focus
                     , down  :: UListDif a focus }
@-}

{-@ type UStack a = {v:Stack a | (Set_emp (Set_cap (listElts (getUp v)) (listElts (getDown v))))} @-}

{-@ measure getUp @-}
getUp :: Stack a -> [a]
getUp (Stack xfocus xup xdown) = xup

{-@ measure getDown @-}
getDown :: Stack a -> [a]
getDown (Stack xfocus xup xdown) = xdown

data Foo a b = J | P a b

--------------------------------------------------------------------------------------
{-@ focusUp :: UStack a -> UStack a @-}
focusUp :: Stack a -> Stack a
focusUp (Stack t [] rs) = Stack xiggety xs []
  where
    P xiggety xs = P t rs
--------------------------------------------------------------------------------------
