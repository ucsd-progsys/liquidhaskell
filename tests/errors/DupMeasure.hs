module DuplicateMeasures where 


{-@ measure lenA :: [a] -> Int 
    lenA [] = 0
    lenA (x:xs) = 1 + lenA xs 
  @-}

{-@ measure lenA :: [a] -> Int 
    lenA [] = 0
    lenA (x:xs) = 1 + lenA xs 
  @-}

{-@ zorg :: {v:[Int] | lenA v == 3} @-}
zorg :: [Int]
zorg = [1,2,3]

