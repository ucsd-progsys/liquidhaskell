module Blank where

-- From
-- http://stackoverflow.com/questions/17501777/implementing-a-zipper-for-length-indexed-lists/17503667#17503667

import Prelude hiding ((++))

{-@ zipper :: zs:[a] -> [(a, {v:[a] | (len v) = (len zs) - 1})] @-}
zipper zs          = go [] zs
  
{-@ Decrease go 2 @-}
{-@ go :: prev:[a] -> rest:[a] -> [(a, {v:[a] | (len v) = (len prev) + (len rest) - 1})] @-}
go _    []     = []
go prev (x:xs) = (x, prev ++ xs) : go (prev ++ [x]) xs

{-@ append :: xs:[a] -> ys:[a] -> {v:[a] | (len v) = (len xs) + (len ys)} @-}
append [] ys     = ys
append (x:xs) ys = x : append xs ys

(++) = append
