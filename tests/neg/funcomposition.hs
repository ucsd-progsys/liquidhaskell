module Foo () where


{-@ cmp1 :: forall < p :: xx:b -> c -> Prop
                  , q :: yy:a -> b -> Prop>.
     (x:b -> c) -> g:(x:a -> b<q x>) -> y:a -> 
      exists[z:b<q y>].c<p z>
 @-}

cmp1 :: (b -> c) -> (a -> b) -> a -> c
cmp1 f g x = f (g x)

{-@ cmp2 :: forall < p :: xx:b -> c -> Prop
                   , q :: yy:a -> b -> Prop>.
     (x:b -> c<p x>) -> g:(x:a -> b) -> y:a -> 
      exists[z:b<q y>].c<p z>
 @-}

cmp2 :: (b -> c) -> (a -> b) -> a -> c
cmp2 f g x = f (g x)

{-@ cmp :: forall < p :: xx:b -> c -> Prop
                   , q :: yy:a -> b -> Prop>.
     (x:b -> c<p x>) -> g:(x:a -> b<q x>) -> y:a -> 
      exists[z:b<q y>].c<p z>
 @-}

cmp :: (b -> c) -> (a -> b) -> a -> c
cmp f g x = f (g x)


{-@ incr2 :: x:Int -> {v:Int|v=x+3} @-}
incr2 :: Int -> Int
incr2 = cmp (+1) (+1)

{-@ incr2' :: x:Int -> {v:Int|v=x+2} @-}
incr2' :: Int -> Int
incr2' = (+1) . (+1)

{-@ qual :: x:Int -> {v:Int|v=x+1} @-}
qual :: Int -> Int
qual = undefined
