module Stacks where

import Data.Set (Set(..)) 

{-@ include <selfList.hquals> @-}

{-@ invariant {v0:[{v: a | (Set_mem v (listElts v0))}] | true } @-}

{- type List a  = {v0: [{v:a | (Set_mem v (listElts v0))}] | true } -}

{-@ type DList a = List<{v: a | (v != fld)}> a @-}

{-@ data Stack a = St { focus  :: a    
                      , up     :: {vu: DList a | (Set_emp (Set_cap (listElts vu) (Set_sng focus))) } 
                      , down   :: {vd: DList a | (Set_emp (Set_cap (listElts vd) (Set_cup (Set_sng focus) (listElts up)))) } 
                      } 
  @-}

data Stack a = St { focus  :: !a    
                  , up     :: ![a] 
                  , down   :: ![a]
                  } deriving (Show, Eq)

{-@ fresh :: a -> Stack a @-}
fresh x = St x [] []

{-@ moveUp :: Stack a -> Stack a @-}
moveUp (St x (y:ys) zs) = St y ys [x] -- (zs)
moveUp s                = s 

-- {- moveDn :: Stack a -> Stack a @-}
-- moveDn (St x ys (z:zs)) = St z (x:ys) zs
-- moveDn s                = s 

