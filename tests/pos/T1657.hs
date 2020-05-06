
module T1657 where

{-@ data I <pigbert :: Int -> Bool> = I Int @-}

data I = I Int
{-@ getI :: forall <pp :: Int -> Bool>. 
             { bloop :: Int <pp> |- {v: Int | v = bloop} <: {v:Int | v > 1984} }
             I <pp>
@-}
getI :: I
getI = undefined 

{-@ pleaseFail :: I<{\v -> v > 1984}> @-}
pleaseFail :: I
pleaseFail = getI
