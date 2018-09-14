module Isort where

data F = F | C Int F  

{-@ data F [lenF] @-}

{-@ measure lenF @-}
lenF :: F -> Int


{-@ lenF :: xs:F -> {v:Int | v >= -1 } @-}
lenF F = 0
lenF (C _ x) = 1 + lenF x 


bar :: F -> Int 
bar F = 0 
bar (C x xs) = x + bar xs 
