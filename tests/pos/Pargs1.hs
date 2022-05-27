{-@ LIQUID "--pruneunsorted" @-}
module Pargs1 () where

{-@ foo :: forall a <p :: x0:Int -> x1:a -> Bool>. 
             (i:Int  -> j : Int-> a<p (i+j)>) -> 
               ii:Int -> jj:Int
              -> a <p (ii+jj)>
  @-}

foo ::  (Int -> Int -> a) -> Int -> Int ->  a
foo f i j = f i j

