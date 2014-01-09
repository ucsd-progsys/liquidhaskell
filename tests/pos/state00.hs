module StateMonad () where

type State = Int
data ST a b = S (b -> (a, b)) | F a | G (b -> a)

{-@ fresh :: ST {v:Int|v>=0} {v:Int|v>=0} @-}
fresh :: ST Int Int
fresh = S $ \n -> (n, n+1)


