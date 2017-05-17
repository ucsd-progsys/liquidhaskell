-- | Sec 9 from Gradual Refinement Types 

module Discussion where
{-@ LIQUID "--gradual" @-}
{-@ LIQUID "--savequery" @-}

{-@ check0 :: x:Int -> {v:Bool | ?? } @-} 
check0 :: Int -> Bool 
check0 = undefined 

{-@ get :: {v:Int | 0 <= v } -> Int @-} 
get :: Int -> Int 
get = undefined 

safe0 x = if check0 x then get x else get (-x)

{-@ assume qual :: x:Int -> {v:Bool | (not v) => (x <= 0)} @-}
qual :: Int -> Bool 
qual = undefined 

{-@ check1 :: x:Int -> {v:Bool | (v => 0 <= x) && (not v => x < 0) } @-} 
check1 :: Int -> Bool 
check1 = undefined 

safe1 x = if check1 x then get x else get (-x)


-- | Part 2 
 
{-@ assume check2 :: x:Int -> {v:Bool | (v => (0 <= x)) && ?? } @-} 
check2 :: Int -> Bool 
check2 = undefined 

safe2 :: Int -> Int 
safe2 x = if check2 x then get x else get (-x)
