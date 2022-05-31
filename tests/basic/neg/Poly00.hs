{-@ LIQUID "--expect-any-error" @-}
module Poly00 where

{-@ zoo :: x:a -> {v:a | v /= x} @-} 
zoo :: goober -> goober 
zoo x = x 
