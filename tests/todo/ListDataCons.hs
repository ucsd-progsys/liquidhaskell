module Fixme where


{-@ hsig :: x:a -> {v:[a] | v == (x:[])} @-} 
hsig :: a -> [a] 
hsig x = [x] 
