{-@ LIQUID "--ple" @-}
-- | Reflection of a function using `quot` and `rem` was not working
-- because they were not defined in the refinement logic until
-- https://github.com/ucsd-progsys/liquidhaskell/pull/2540
-- to fix
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1447

module QuotRemInt where

{-@ reflect intId @-}
intId :: Int -> Int
intId x = (x `quot` 2) * 2 + (x `rem` 2)

{-@ reflect intId' @-}
intId' :: Int -> Int
intId' x = (x `div` 2) * 2 + (x `mod` 2)

{-@ lemmaQuotRem :: x:Int -> {intId x == x } @-}
lemmaQuotRem :: Int -> ()
lemmaQuotRem _ = ()


{-@ lemmaDivMod :: x:Int -> { intId' x = x } @-}
lemmaDivMod :: Int -> ()
lemmaDivMod  _ = ()

{-@
examplesQuot
   :: { -2 = quot (-5) 2 &&
        -2 = quot 5 (-2) &&
        2 = quot 5 2 &&
        0 = quot 0 2 &&
        0 = quot 1 2 &&
        0 = quot (-1) 2 &&
        0 = quot 1 (-2)
      }
@-}
examplesQuot :: ()
examplesQuot = ()

{- This cases resulted in a Liquid Type Mismatch...
they fail as well for div, so it
seems that logic @/@ is not like Haskell 'div'.

        2 = quot (-5) (-2) &&
        0 = quot (-1) (-2)
-}

{-@
examplesRem
   :: { -1 = rem (-5) 2 &&
        1 = rem 5 (-2) &&
        1 = rem 5 2 &&
        0 = rem 0 2 &&
        0 = rem 0 (-2) &&
        1 = rem 1 2 &&
        -1 = rem (-1) 2 &&
        1 = rem 1 (-2)
      }
@-}
examplesRem :: ()
examplesRem = ()

{- This cases resulted in a Liquid Type Mismatch...
they fail as well for mod, so it
seems that logic @mod@ is not like Haskell 'mod'.

        -1 = rem (-5) (-2) &&
        -1 = rem (-1) (-2)
-}

{- For a neg test:

{-@ examplesDiv :: { 2 = (-5) / (-2)} @-}
examplesDiv :: ()
examplesDiv = ()

{-@ examplesDiv :: { 2 = (-5) mod (-2)} @-}
examplesMod :: ()
examplesMod = ()
-}
