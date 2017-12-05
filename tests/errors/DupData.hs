-- | See https://github.com/ucsd-progsys/liquidhaskell/issues/1175

module BadVec where

data OVec a = ONil
            | (:>>) {oHd :: a, oTl :: OVec a}
infixr 5 :>>

{-@ data OVec a = ONil
               | (:>>) {oHd :: a,
                        oTl :: OVec {v:a | v >= oHd}} @-}


{-@ data OVec [mylen] @-}
{-@ measure mylen @-}
{-@ mylen :: OVec a -> Nat @-}
mylen :: OVec a -> Int
mylen ONil       = 0
mylen (_ :>> xs) = 1 + mylen xs

{-@ badVec :: OVec Int @-}
badVec :: OVec Int
badVec = 1 :>> 3 :>> 2 :>> ONil

