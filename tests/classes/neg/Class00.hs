{-@ LIQUID "--expect-any-error" @-}
module Class00 where

class Zoo a where 
  zoo :: Int -> a 

{-@ class Zoo a where 
      zoo :: {v:Int | v > 0} -> a 
  @-}

zing :: (Zoo a) => a 
zing = zoo 0 

