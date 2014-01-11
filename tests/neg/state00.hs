module StateMonad () where

type State = Int
data ST a b = S (a -> (a, b)) | F a

{-@ fresh :: ST Int {v:Int|v>=0} @-}
fresh :: ST Int Int
fresh = S $ \n -> (n, n+1)


