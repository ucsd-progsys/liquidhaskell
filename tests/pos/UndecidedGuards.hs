-- Tests that --ple-with-undecided-guards has an effect on verification
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--ple" @-}

module UndecidedGuards where

{-@ reflect boolToInt @-}
boolToInt :: Bool -> Int
boolToInt False = 0
boolToInt True = 1

-- | This property would usually not be provable without spliting in cases
-- because PLE doesn't unfold @boolToInt@ if @b@ is not known to be empty
-- or non-empty. But here @--ple-with-undecided-guards@ is in effect, so
-- @boolToInt@ is expanded anyway.
--
{-@ nonNegativeInt :: b:_ -> { boolToInt b >= 0 } @-}
nonNegativeInt :: Bool -> ()
nonNegativeInt _ = ()
