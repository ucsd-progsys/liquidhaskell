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



-- All of the below violate the invariant, get liquid to say so!

bad0 x = St x [x] []
bad1 x = St x []  [x]
bad2 x = St 0 [x] [x]
bad3 x = St x [1] [1] 

