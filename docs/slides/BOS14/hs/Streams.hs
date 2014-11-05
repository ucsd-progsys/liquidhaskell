module Streams where

import Prelude hiding (take, repeat)

import Language.Haskell.Liquid.Prelude

-------------------------------------------------------------------------
-- | Lists 
-------------------------------------------------------------------------
 
data List a = N | C { x :: a, xs :: List a }

-- | Associate an abstract refinement with the _tail_ xs

{-@ data List a <p :: List a -> Prop>
      = N | C { x  :: a
              , xs :: List <p> a <<p>>
              }
  @-}

-------------------------------------------------------------------------
-- | Infinite Streams
-------------------------------------------------------------------------

-- | Infinite List = List where _each_ tail is a `cons` ...

{-@ type Stream a = {xs: List <{\v -> cons v}> a | cons xs} @-}

-- | A simple measure for when a `List` is a `Cons`

{-@ measure cons  :: (List a) -> Prop
    cons (C x xs) = true 
    cons (N)      = false 
  @-}

-------------------------------------------------------------------------
-- | Creating an Infinite Stream
-------------------------------------------------------------------------

{-@ Lazy repeat @-}
                 
{-@ repeat :: a -> Stream a @-}
repeat   :: a -> List a
repeat x = x `C` repeat x


-------------------------------------------------------------------------
-- | Using an Infinite Stream
-------------------------------------------------------------------------

{-@ take        :: n:Nat -> Stream a -> {v:List a | size v = n} @-}
take 0 _        = N
take n (C x xs) = x `C` take (n-1) xs
take _ N        = liquidError "never happens"

-------------------------------------------------------------------------











-- | Other specs from before ...

{-@ measure size :: List a -> Int 
    size (N)      = 0
    size (C x xs) = (1 + size xs)
  @-}






















-----------------------------------------------------
take            :: Int -> List a -> List a









