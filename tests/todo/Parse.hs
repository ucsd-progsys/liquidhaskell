module Fixme where


data L a
  = C {x :: a , xs :: L a} 

{-@ data L a 
   = C { x:: a , xs :: L a} 
 @-}
