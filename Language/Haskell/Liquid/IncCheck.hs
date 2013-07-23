module Language.Haskell.Liquid.IncCheck (lineDiff) where

import Control.Applicative ((<$>))
import Data.Algorithm.Diff

lineDiff :: String -> String -> IO [Int]
lineDiff f1 f2 
  = do s1 <- getLines f1
       s2 <- getLines f2
       return $ diffLines 1 $ getGroupedDiff s1 s2

diffLines _ []              = []
diffLines n (Both ls _ : d) = diffLines n' d                         where n' = n + length ls
diffLines n (First ls : d)  = [n .. (n' - 1)] ++ diffLines n' d      where n' = n + length ls
diffLines n (Second ls : d) = diffLines n d 

getLines = fmap lines . readFile
