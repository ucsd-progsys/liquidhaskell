module Interpreter where 

{-@ measure progDenote @-}
progDenote :: [a] -> [Int]
progDenote (x:xs) = [2] 

