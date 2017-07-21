{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}

module Fixme where

import Prelude hiding (map, concatMap)

{-@ reflect bob @-}
bob :: L a -> Int 
bob Emp     = 0
bob (Goo x) = 1 

{-@ goo :: x:{L Int | x = Emp} -> { bob x = bob Emp} @-}
goo :: L Int -> () 
goo x = ()

data L a = Emp | Goo a 
{-@ data L a = Emp | Goo { lHd :: a } @-}

