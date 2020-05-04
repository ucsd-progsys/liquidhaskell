{-@ data I <p :: Int -> Bool> = I _ @-}
data I = I Int

{-@ getI :: forall <p :: Int -> Bool>. 
             { {x: Int<p> | True} <: {x:Int | x > 0} }
             I <p>
@-}
getI :: I
getI = undefined 

{-@ pleaseFail :: I<{\_ -> True}> @-}
pleaseFail :: I
pleaseFail = getI