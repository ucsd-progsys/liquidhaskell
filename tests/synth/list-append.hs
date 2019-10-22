{-@ LIQUID "--typed-holes" @-}

module Append where 

import Data.Set 

{-@ type OList a = [a]<{\h v -> h <= v }> @-}

{-@ append' :: xs: OList a -> ys: OList a  -> {v:OList a | len v == len xs + len ys && listElts v == union (listElts xs) (listElts ys) } @-}
append' :: [a] -> [a] -> [a]
append' x0 x1 = -- _append
    case x0 of 
        [] -> x1
        x2 : x3 -> _appendCons


{- 
append [] xs = xs 
append (y:ys) xs = y:append ys xs 

append x0 x1 = 
    case x0 of 
        []      -> x1
        x2 : x3 -> x2 : append x3 x1


append xs [] = xs 
append [] ys = ys 
append (x:xs) (y:ys) = y:append xs ys
-- append xs ys =
--  case ys of
--      [] -> xs
--      x3 : x4 ->
--          case xs of
--              [] -> ys
--              x7 : x8 -> x3 : (append x8 ys)
-}