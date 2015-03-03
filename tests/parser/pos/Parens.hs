module Parens where

{-@ data Node a = Branch (BranchList a) @-}
data Node a = Branch (BranchList a)
data BranchList a = BL a

{-@ test :: v:a -> (a, a) @-}
test :: a -> (a,a)
test x = (x,x)

{-@
measure listlen :: [a] -> Int
listlen [] = 0
listlen (x:xs) = 1 + listlen xs
@-}
