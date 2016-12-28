module MapReduce where

{-@ data List [llen] a = N | C {lhead :: a, ltail :: List a} @-}
data List a = N | C a (List a)

{-@ measure llen @-}
llen :: List a -> Bool 
llen N = True  
llen (C _ xs) = False -- 1 + llen xs


{-@ data List2 [llen2] a = N2 | C2 {lhead2 :: a, ltail2 :: List2 a} @-}
data List2 a = N2 | C2 a (List2 a)
