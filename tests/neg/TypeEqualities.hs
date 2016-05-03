{-# LANGUAGE TypeFamilies   #-}

{-@ zoo :: x:a -> y:a -> {v:b | v ~~ y} @-}
zoo :: (a~b) => a -> a -> b 
zoo x _ = x 
