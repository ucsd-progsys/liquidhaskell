-- This test checks whether "invariants" are getting imported.

module List02 where

import List02Lib 

{-@ bloop :: xs:List a -> {v:Int | v = size xs} -> NN @-}
bloop :: List a -> Int -> Int 
bloop xs n = n 

imports = ( size )
