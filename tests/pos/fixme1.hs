module StateMonad where

data ST a = S (Int -> (a, Int))
{-@ data ST a <p1 :: old:Int -> a -> Prop> 
     = S (x::(state:Int -> (a<p1 state>, Int))) 
  @-}


{-@
apply :: forall a <p1 :: old:Int -> a -> Prop>.
          instate:(ST a <p1>) -> x:Int -> (a<p1 x>, Int)
  @-}
apply :: ST a -> Int -> (a, Int)
apply (S f) x = f x

