module ReWrite7 where
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ reflect f @-}
f :: [Int] -> Bool
f []      = True
f (x:xs) = f xs

{-@ fp :: xs : [Int] -> { f xs = True } @-}
fp :: [Int] -> ()
fp []     = ()
fp (x:xs) = fp xs

{-@ rewrite bad @-}
{-@ bad :: x : [Int] -> y : [Int] -> { f x = f y } @-}
bad :: [Int] -> [Int] -> ()
bad [] []        = ()
bad (x:xs) ys    = bad xs ys
bad []    (y:ys) = bad [] ys
