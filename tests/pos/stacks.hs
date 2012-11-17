module Stacks where

import Data.Set (Set(..)) 

{-@ type IList a = {v0: [{v:a | (Set_mem v (listElts v0))}] | true } @-}

{-@ type DList a = IList<{v: a | (v != fld)}> a @-}

{-@ data Stack a = St { focus  :: a    
                      , up     :: DList {v: a | v != focus}
                      , down   :: DList {v: a | v != focus}
                      } 
  @-}

data Stack a = St { focus  :: !a    
                  , up     :: ![a] 
                  , down   :: ![a]
                  } deriving (Show, Eq)

{-@ fresh :: a -> Stack a @-}
fresh x = St x [] []

{-@ moveUp :: Stack a -> Stack a @-}
moveUp (St x (y:ys) zs) = St y ys (x:zs)
moveUp s                = s 

{-@ moveDn :: Stack a -> Stack a @-}
moveDn (St x ys (z:zs)) = St z (x:ys) zs
moveDn s                = s 

