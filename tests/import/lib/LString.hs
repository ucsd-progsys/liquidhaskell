{-@ LIQUID "--reflection" @-}

module LString where 

{-@ reflect myhead @-}
{-@ myhead :: {v:[a] | 0 < len v } -> Bool @-}
myhead :: [a] -> Bool
myhead (x:xs) = True  
myhead _ = impossible False "this should crash"

{-@ reflect impossible @-}
impossible :: a -> String -> a 
{-@ impossible :: a -> {v:String | false } -> a @-}
impossible a _ = a 