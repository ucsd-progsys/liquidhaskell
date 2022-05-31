{-@ LIQUID "--expect-any-error" @-}
module T1657 where

{-@ data I <p :: Int -> Bool> = I _ @-}
data I = I Int

{-@ getI :: forall <p :: Int -> Bool>. 
             { {x: Int<p> | True} <: {x:Int | x > 0} }
             I <p>
@-}
getI :: I
getI = I 7  

{-@ shouldPass :: I<{\z -> true}> @-}
shouldPass :: I
shouldPass = getI
