module Fixme where

data L a = N 


{-@ lnil :: {v:L a | v == Fixme.N } @-} 
lnil :: L a 
lnil = N

{-@ hnil :: {v:[a] | v == []} @-} 
hnil :: [a] 
hnil = [] 

{-@ (:) :: x:a -> xs:[a] -> {v:[a] |  v == x:xs} @-}

{-@ hcons :: x:a -> xs:[a] -> {v:[a] | v == x:xs} @-} 
hcons :: a -> [a] -> [a] 
hcons = (:)