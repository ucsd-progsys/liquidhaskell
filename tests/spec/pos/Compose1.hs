-- override the input spec
{-@ assume GHC.Base.. :: (b -> c) -> (a -> b) -> a -> c @-}

{-@ incr :: Nat -> Nat @-}
incr :: Int -> Int 
incr x = x + 1

{-@ incr2 :: Nat -> Nat @-}
incr2 = incr . incr 
