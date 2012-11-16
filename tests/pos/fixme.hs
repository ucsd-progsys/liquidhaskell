module Ex where

data Vec a = Nil

{-@ efoldr :: forall b a <p :: x0:Vec a -> x1:b -> Bool>. 
                 (exists [w:{v:Vec a | v = (Ex.Nil)}] . (b <p w>))
              -> ys : Vec a
              -> b <p ys>
  @-}
efoldr :: b -> Vec a -> b
efoldr b Nil         = b
