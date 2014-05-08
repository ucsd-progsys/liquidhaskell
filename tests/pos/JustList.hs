module Foo where

{-@
data F a b <p :: (B a) -> Prop> = F { bx :: b
               , by :: [< (B a) <p> > ]
               } 
  @-}
{-@
data B a = B {wp :: Maybe a}
  @-}
data F a b = F { bx :: b
               , by :: [B a]
               } 

data B a = B {wp :: Maybe a}


foo = F
b = B
{-@ bar :: F <{\v -> (isJust (wp v))}> a b -> {v:Bool | (Prop v) }@-}
bar :: F a b -> Bool
bar (F x ((B (Just y)):_)) = True
bar (F x [] ) = True
bar _ = False 


isJust (Just x) = True
isJust _        = False
