{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--ple" @-}

-- | A reflected function using `quot` and `rem` seems to not
-- be properly unfolded.

module QuotRemInt where

{-@ reflect intId @-}
intId :: Int -> Int
intId x = (x `quot` 2) * 2 + (x `rem` 2)

{-@ lemmaQuotRem :: x:Int -> { intId x = x } @-}
lemmaQuotRem :: Int -> ()
lemmaQuotRem _ = ()
