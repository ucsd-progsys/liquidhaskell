module TellingLies where

import Prelude  hiding (repeat)
import Language.Haskell.Liquid.Prelude (liquidAssert)

-- | Why is Termination Analysis Required

{-@ Lazy foo @-}
{-@ foo :: Int -> {v:Int | false} @-}
foo     :: Int -> Int
foo n   = foo n


prop = liquidAssert ((\_ -> 0==1) (foo 0))

-- | Turning off Termination Checking

{-@ Lazy repeat @-}
{-@ repeat :: a -> [a] @-}
repeat     :: a -> [a]
repeat a   = a : repeat a
