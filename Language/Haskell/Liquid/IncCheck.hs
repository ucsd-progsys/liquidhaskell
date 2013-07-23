-- | This module contains the code for Incremental checking, which finds the 
--   part of a target file (the subset of the @[CoreBind]@ that have been 
--   modified since it was last checked (as determined by a diff against
--   a saved version of the file. 

module Language.Haskell.Liquid.IncCheck (slice) where

import Control.Applicative ((<$>))
import Data.Algorithm.Diff

slice :: FilePath -> [CoreBind] -> IO [CoreBind] 
slice target cbs
  = do is    <- changedLines target
       xs    <- diffVars is defs
       ys    <- dependentVars deps xs
       return $ filterBinds cbs ys
    where 
       deps   = coreDeps cbs
       defs   = coreDefs cbs

filterBinds :: [CoreBind] -> [Var] -> [CoreBind]
filterBinds = error "TODO"

coreDefs :: [CoreBind] -> [Def]
coreDefs = error "TODO"

coreDeps :: [CoreBind] -> Deps
coreDeps = error "TODO"

dependtVars :: Deps -> [Var] -> [Var]
dependentVars d xs = error "TODO: return (closed) list of binders on which xs depend"

data Def  = D { start :: Int, end :: Int, binder :: Var }
            deriving (Eq, Ord, Show)

type Deps = M.HashMap Var [Var]

diffVars :: [Int] -> [Def] -> [Var]
diffVars lines defs = error "TODO"

-------------------------------------------------------------------------
-- Diff Interface -------------------------------------------------------
-------------------------------------------------------------------------

changedLines :: FilePath -> IO [Int]
changedLines = error "TODO"

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
