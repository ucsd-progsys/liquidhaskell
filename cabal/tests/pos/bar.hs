module Bar where

import Language.Haskell.Liquid.Prelude
{-
prop1 =let f x = x+1 in
       let s = f $ 3 in 
       let s1 = (\x -> x - 1) $ 4 in
       assert (s > 3 && s1 < 4) 
-}
prop = let s = (\x -> x+1) $ 3 in 
       let s1 = (\x -> x - 1) $ 4 in
       assert (s > 3 && s1 < 4) 

