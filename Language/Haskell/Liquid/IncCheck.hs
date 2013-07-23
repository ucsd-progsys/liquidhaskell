-- | This module contains the code for Incremental checking, which finds the 
--   part of a target file (the subset of the @[CoreBind]@ that have been 
--   modified since it was last checked (as determined by a diff against
--   a saved version of the file. 

module Language.Haskell.Liquid.IncCheck (slice, save) where

import            Control.Applicative          ((<$>))
import            Data.Algorithm.Diff
import            CoreSyn                      
-- import            Outputable 
import            Var 
import qualified  Data.HashSet                 as S    
import qualified  Data.HashMap.Strict          as M    
import qualified  Data.List                    as L
import            Data.Function                (on)
import            System.Directory             (copyFile, doesFileExist)

import            Language.Fixpoint.Files
import            Language.Haskell.Liquid.GhcInterface
import            Language.Haskell.Liquid.GhcMisc
import            Text.Parsec.Pos              (sourceLine) 

-- | `slice` returns a subset of the @[CoreBind]@ of the input `target` 
--    file which correspond to top-level binders whose code has changed 
--    and their transitive dependencies.
-------------------------------------------------------------------------
slice :: FilePath -> [CoreBind] -> IO [CoreBind] 
-------------------------------------------------------------------------
slice target cbs
  = do let saved = extFileName Saved target
       ex  <- doesFileExist saved 
       if ex then do is    <- tracePpr "INCCHECK: changed lines" <$> lineDiff target saved
                     let xs = diffVars is   (coreDefs cbs) 
                     let ys = dependentVars (coreDeps cbs) (S.fromList xs)
                     return $ filterBinds cbs ys
             else return cbs 

-------------------------------------------------------------------------
filterBinds        :: [CoreBind] -> S.HashSet Var -> [CoreBind]
-------------------------------------------------------------------------
filterBinds cbs ys = filter f cbs
  where 
    f (NonRec x _) = x `S.member` ys 
    f (Rec xes)    = any (`S.member` ys) $ fst <$> xes 

-------------------------------------------------------------------------
coreDefs     :: [CoreBind] -> [Def]
-------------------------------------------------------------------------
coreDefs cbs = mkDefs lxs 
  where 
    lxs      = L.sortBy (compare `on` fst) [(line x, x) | x <- xs ]
    xs       = concatMap bindersOf cbs
    line     = sourceLine . getSourcePos 

mkDefs []          = []
mkDefs ((l,x):lxs) = case lxs of
                       []       -> [D l Nothing x]
                       (l',_):_ -> (D l (Just l') x) : mkDefs lxs

data Def  = D { start  :: Int
              , end    :: Maybe Int
              , binder :: Var 
              } 
            deriving (Eq, Ord)
              
instance Show Def where 
  show (D i j x) = "var " ++ showPpr x ++ " start: " ++ show i ++ " end: " ++ show j

-------------------------------------------------------------------------
coreDeps  :: [CoreBind] -> Deps
-------------------------------------------------------------------------
coreDeps  = M.fromList . concatMap bindDep 

bindDep b = [(x, ys) | x <- bindersOf b]
  where 
    ys    = S.fromList $ freeVars S.empty b

type Deps = M.HashMap Var (S.HashSet Var)

-------------------------------------------------------------------------
dependentVars :: Deps -> S.HashSet Var -> S.HashSet Var
-------------------------------------------------------------------------
dependentVars d xs = tracePpr "INCCHECK: tx changed vars" $ go S.empty (tracePpr "INCCHECK: seed changed vars" xs)
  where 
    pre            = S.unions . fmap deps . S.toList
    deps x         = M.lookupDefault S.empty x d
    go seen new 
      | S.null new = seen
      | otherwise  = let seen' = S.union seen new
                         new'  = pre new `S.difference` seen'
                     in go seen' new'

-------------------------------------------------------------------------
diffVars :: [Int] -> [Def] -> [Var]
-------------------------------------------------------------------------
diffVars lines defs  = go (L.sort lines) (L.sort defs)
  where 
    go _      []     = []
    go []     _      = []
    go (i:is) (d:ds) 
      | i `lt` d     = go is (d:ds)
      | i `gt` d     = go (i:is) ds
      | otherwise    = binder d : go is ds 

lt i d               = i < start d
gt i d               = maybe False (i >) (end d)
-------------------------------------------------------------------------
-- Diff Interface -------------------------------------------------------
-------------------------------------------------------------------------

-- | `save` creates an .saved version of the `target` file, which will be 
--    used to find what has changed the /next time/ `target` is checked.
-------------------------------------------------------------------------
save :: FilePath -> IO ()
-------------------------------------------------------------------------
save target = copyFile target $ extFileName Saved target


-- | `lineDiff src dst` compares the contents of `src` with `dst` 
--   and returns the lines of `src` that are different. 
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
diffLines n (Second _ : d)  = diffLines n d 

getLines = fmap lines . readFile
