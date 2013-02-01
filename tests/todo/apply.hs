module StateMonad where

data ST a = S (Int -> (a, Int))
{-@ data ST a <p1 :: old:Int -> a -> Prop,
               p2 :: old:Int -> Int -> Prop> 
     = S (x::(state:Int -> (a<p1 state>, Int<p2 state>))) 
  @-}


{-@
apply :: forall a <p1 :: old:Int -> a -> Prop, 
                   p2 :: old:Int -> Int -> Prop>.
          instate:(ST a) <p1, p2> -> x:Int -> (a<p1 x>, Int<p2 x>)
  @-}
apply :: ST a -> Int -> (a, Int)
apply (S f) x = f x

