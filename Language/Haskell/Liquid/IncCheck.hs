-- | This module contains the code for Incremental checking, which finds the 
--   part of a target file (the subset of the @[CoreBind]@ that have been 
--   modified since it was last checked (as determined by a diff against
--   a saved version of the file. 

module Language.Haskell.Liquid.IncCheck (slice, save) where

import            Control.Applicative          ((<$>))
import            Data.Algorithm.Diff
import            Name                         (getSrcSpan)
import            SrcLoc                       (srcSpanFile, srcSpanStartLine, srcSpanStartCol)
import            CoreSyn                      (bindersOf)
import qualified  Data.HashSet                 as S    
import qualified  Data.HashMap.Strict          as M    
import qualified  Data.List                    as L
import            Language.Fixpoint.Files
import            System.Directory             (copyFile)

-- | `slice` returns a subset of the @[CoreBind]@ of the input `target` 
--    file which correspond to top-level binders whose code has changed 
--    and their transitive dependencies.
-------------------------------------------------------------------------
slice :: FilePath -> [CoreBind] -> IO [CoreBind] 
-------------------------------------------------------------------------
slice target cbs
  = do is    <- changedLines target
       let xs = diffVars is   (coreDefs cbs) 
       let ys = dependentVars (coreDeps cbs) (S.fromList xs)
       return $ filterBinds cbs ys

-------------------------------------------------------------------------
filterBinds        :: [CoreBind] -> S.Set Var -> [CoreBind]
-------------------------------------------------------------------------
filterBinds cbs ys = filter f cbs
  where 
    f (NonRec x _) = x `S.member` ys 
    f (Rec xes)    = any (`S.member` ys) $ fst <$> xes 

-------------------------------------------------------------------------
coreDefs :: [CoreBind] -> [Def]
-------------------------------------------------------------------------
coreDefs = mkDefs lxs 
  where 
    lxs  = L.sortBy (compare `on` fst) [(line x, x) | x <- xs ]
    xs   = concatMap bindersOf cbs
    line = srcSpanStartLine . getSrcSpan 

mkDefs []          = []
mkDefs ((l,x):lxs) = case lxs of
                       []       -> [D l Nothing x]
                       (l',_):_ -> (D l (Just l') x) : mkDefs lxs

data Def  = D { start :: Int, end :: Maybe Int, binder :: Var } 
            deriving (Eq, Ord, Show)
               
-------------------------------------------------------------------------
coreDeps  :: [CoreBind] -> Deps
-------------------------------------------------------------------------
coreDeps  = M.fromList . map bindDep 

bindDep b = [(x, ys) | x <- bindersOf b]
  where 
    ys    = S.fromList $ freeVars S.empty b

type Deps = M.HashMap Var (S.HashSet Var)

-------------------------------------------------------------------------
dependentVars :: Deps -> S.Set Var -> S.Set Var
-------------------------------------------------------------------------
dependentVars d xs = go S.empty xs
  where 
    pre            = unions . fmap deps . S.elems
    deps x         = M.lookupDefault S.empty x d
    go seen new 
      | S.null new = seen
      | otherwise  = let seen' = S.union seen new
                         new'  = pre new `S.difference` seen'
                     in go seen' new'

-------------------------------------------------------------------------
diffVars :: [Int] -> [Def] -> [Var]
-------------------------------------------------------------------------
diffVars lines defs  = go (sort lines) (sort defs)
  where 
    go _      []     = []
    go []     _      = []
    go (i:is) (d:ds) 
      | i < start d  = go is (d:ds)
      | i > end d    = go (i:is) ds
      | otherwise    = binder d : go is ds 

-------------------------------------------------------------------------
-- Diff Interface -------------------------------------------------------
-------------------------------------------------------------------------

-- | `save` creates an .saved version of the `target` file, which will be 
--    used to find what has changed the /next time/ `target` is checked.
-------------------------------------------------------------------------
save :: FilePath -> IO ()
-------------------------------------------------------------------------
save target = copyFile target (target `extFileName` Saved)


-- | `changedLines target` compares the contents of `target` with 
--   its `save` version to determine which lines are different.
-------------------------------------------------------------------------
changedLines :: FilePath -> IO [Int]
-------------------------------------------------------------------------
changedLines target = lineDiff target $ target `extFileName` Saved

-------------------------------------------------------------------------
lineDiff :: FilePath -> FilePath -> IO [Int]
-------------------------------------------------------------------------
lineDiff src dst 
  = do s1 <- getLines src 
       s2 <- getLines dst
       return $ diffLines 1 $ getGroupedDiff s1 s2

diffLines _ []              = []
diffLines n (Both ls _ : d) = diffLines n' d                         where n' = n + length ls
diffLines n (First ls : d)  = [n .. (n' - 1)] ++ diffLines n' d      where n' = n + length ls
diffLines n (Second ls : d) = diffLines n d 

getLines = fmap lines . readFile
