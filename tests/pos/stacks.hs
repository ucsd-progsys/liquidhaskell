module Stacks where

{-@ type DList a = [a]<{v: a | (v != fld)}> @-}

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

