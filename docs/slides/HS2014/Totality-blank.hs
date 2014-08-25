{-@ LIQUID "--no-termination" @-}
{- LIQUID "--totality"       @-}
module Totality where

import Prelude hiding (head)
import Language.Haskell.Liquid.Prelude
import Control.Exception.Base

head (x:_) = x




































safeZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
safeZipWith f = go
  where
    go (x:xs) (y:ys) = f x y : go xs ys
    go []     []     = []






































nestcomment :: Int -> String -> (String,String)
nestcomment n ('{':'-':ss) | n>=0 = (("{-"++cs),rm)
                                  where (cs,rm) = nestcomment (n+1) ss
nestcomment n ('-':'}':ss) | n>0  = let (cs,rm) = nestcomment (n-1) ss
                                    in (("-}"++cs),rm)
nestcomment n ('-':'}':ss) | n==0 = ("-}",ss)
nestcomment n (s:ss)       | n>=0 = ((s:cs),rm)
                                  where (cs,rm) = nestcomment n ss
nestcomment n [] = ([],[])












-- Local Variables:
-- flycheck-checker: haskell-liquid
-- End:
