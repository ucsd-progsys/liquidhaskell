{-@ LIQUID "--expect-any-error" @-}
module T1657A where

{-@ data I <pigbert :: Int -> Bool> = I Int @-}

data I = I Int
{-@ getI :: forall <pp :: Int -> Bool>. 
             { bloop :: Int <pp> |- {v: Int | v = bloop} <: {v:Int | v > 1984} }
             I <pp>
@-}
getI :: I
getI = undefined 

-- { {v: (Int<p>) | True} <: {v:Int | v > 1984} }

{-@ pleaseFail :: I<{\_ -> True}> @-}
pleaseFail :: I
pleaseFail = getI
