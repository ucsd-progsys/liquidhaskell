module AnalyzeLogs (collate) where

import           Data.CSV.Table
import           Text.CSV
import qualified Data.List as L

-- | Usage:
--      ghci> collate ["summary-1.csv", "summary-2.csv", ... , "summary-n.csv"] "out.csv"
--
--------------------------------------------------------------------------------
collate :: [FilePath] -> FilePath -> IO Table
--------------------------------------------------------------------------------
collate fs f = do
  ts    <- mapM load fs
  let t  = transform ts
  toFile f t
  return t

--------------------------------------------------------------------------------
load :: FilePath -> IO Table
--------------------------------------------------------------------------------
load f = mkTable f <$> readFile f

mkTable :: FilePath -> String -> Table
mkTable f s = fromString f $ unlines (hdr : body)
  where
    hdr     = "test, time-" ++ stamp ++ ",result"
    body    = drop 6 ls
    stamp   = drop 17 (ls !! 2)
    ls      = lines s

--------------------------------------------------------------------------------
transform :: [Table] -> Table
--------------------------------------------------------------------------------
transform = sortBy rngC FInt Dsc
          . addRange
          . foldr1 join
          . map hideResult

hideResult :: Table -> Table
hideResult t = hide t [C "result"]

addRange :: Table -> Table
addRange = newColumn rngC range

rngC :: Col
rngC = C "range"

range :: RowInfo -> Field
range cvs = show $ truncate (hi - lo)
  where
    vs    = [ read v :: Double | (C c, v) <- cvs, "time-" `L.isInfixOf` c ]
    lo    = minimum vs
    hi    = maximum vs
