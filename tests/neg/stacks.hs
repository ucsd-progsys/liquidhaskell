module Stacks () where


{-@ type DList a = [a]<{\fld v -> (v != fld)}> @-}

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

{-@ bad0 :: a -> Stack a @-}
bad0   :: a -> Stack a 
bad0 x = St x [x] []


{-@ bad1 :: a -> Stack a @-}
bad1   :: a -> Stack a 
bad1 x = St x []  [x]

{-@ bad2 :: Int -> Stack Int @-}
bad2 :: Int -> Stack Int
bad2 x = St 0 [x] [x]

{-@ bad2 :: Int -> Stack Int @-}
bad3 :: Int -> Stack Int
bad3 x = St x [1] [1] 

