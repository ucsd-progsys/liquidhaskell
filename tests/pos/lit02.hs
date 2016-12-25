module Goo where 

import Data.Set as S 

{-@ predicate ValidMovieScheme V =
	  ((listElts V == Set_cup (Set_sng "year")
	  	                      (Set_cup (Set_sng "star")
	  	                      (Set_cup (Set_sng "director")
	  	                               (Set_sng "title"))))) @-}

{-@ foo :: xs:[String] -> {ys: [String] | Set_sub (listElts xs) (listElts ys)} -> Int @-}
foo :: [String] -> [String] -> Int 
foo = undefined

{-@ assume things :: {v:[String] | ValidMovieScheme v} @-}
things :: [String] 
things = undefined 

bar = foo ["director"] things 
