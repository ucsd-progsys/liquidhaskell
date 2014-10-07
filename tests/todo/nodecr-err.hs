module Poo where

import Prelude hiding (map, foldr, foldr1)

data List a = N | C a (List a)

-- this should be flagged as an ERROR (UNSAFE) not a warning.

map f (N)      = N
map f (C x xs) = C (f x) (map f xs) 

