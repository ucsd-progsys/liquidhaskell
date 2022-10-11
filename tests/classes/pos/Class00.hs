module Class00 where

class Zoo a where 
  zoo :: a -> Int 

{-@ class Zoo a where 
      zoo :: a -> {v:Int | v > 0} 
  @-}

{-@ zing :: (Zoo a) => a -> {v:Int | v > 0} @-} 
zing x = zoo x 

