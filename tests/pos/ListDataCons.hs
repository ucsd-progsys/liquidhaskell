module Fixme where

data L a = N 


{-@ lnil :: {v:L a | v == Fixme.N } @-} 
lnil :: L a 
lnil = N

{-@ hnil :: {v:[a] | v == []} @-} 
hnil :: [a] 
hnil = [] 

{- hsig :: x:a -> {v:[a] | v == [x]} @-} 
hsig :: a -> [a] 
hsig x = [x] 

{-@ hcons :: x:a -> xs:[a] -> {v:[a] | v == x:xs} @-} 
hcons :: a -> [a] -> [a] 
hcons = (:)