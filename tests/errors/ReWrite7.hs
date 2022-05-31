{-@ LIQUID "--expect-error-containing=Could not generate any rewrites from equality" @-}
module ReWrite7 where
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ reflect f @-}
f :: [Int] -> Bool
f []      = True
f (x:xs) = f xs

-- Reject both sides with free vars
{-@ rewrite bad @-}
{-@ bad :: x : [Int] -> y : [Int] -> { f x = f y } @-}
bad :: [Int] -> [Int] -> ()
bad [] []        = ()
bad (x:xs) ys    = bad xs ys
bad []    (y:ys) = bad [] ys
