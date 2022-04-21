
-- | A somewhat fancier example demonstrating the use of Abstract Predicates and exist-types

module Ex01 () where


-------------------------------------------------------------------------
-- | Data types ---------------------------------------------------------
-------------------------------------------------------------------------

data Vec a = Nil 

{-@ efoldr :: forall b a <p :: x0:Vec a -> x1:b -> Bool>. 
              b <p Ex01.Nil>
              -> ys: Vec a
              -> b <p ys>
  @-}
efoldr :: b -> Vec a -> b
efoldr b Nil         = b

