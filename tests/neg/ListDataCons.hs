module Fixme where

data L a = N 


{-@ lnil :: {v:L a | v == Fixme.N } @-} 
lnil :: L a 
lnil = N

{-@ hnil :: {v:[Int] | v == []} @-} 
hnil :: [Int] 
hnil = [0] 

{-@ hsig :: x:a -> a -> {v:[a] | v == [x]} @-} 
hsig :: a -> a -> [a] 
hsig _ x = [x] 

{-@ hcons :: x:a -> a -> xs:[a] -> {v:[a] | v == x:xs} @-} 
hcons :: a -> a -> [a] -> [a] 
hcons _ = (:)