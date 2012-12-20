
-- | A somewhat fancier example demonstrating the use of Abstract Predicates and exist-types

module Ex where


-------------------------------------------------------------------------
-- | Data types ---------------------------------------------------------
-------------------------------------------------------------------------

data Vec a = Nil | Cons a (Vec a)

{-@ efoldr :: forall b a <p :: x0:Vec a -> x1:b -> Bool>. 
              (exists [zz: {v: Vec a | v = Ex.Nil}]. b <p zz>) 
              -> ys: Vec a
              -> b <p ys>
  @-}
efoldr :: b -> Vec a -> b
efoldr b Nil         = b

