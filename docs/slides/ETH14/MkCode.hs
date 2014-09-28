#!/usr/bin/env runhaskell

import System.Environment   (getArgs)
import System.FilePath      (replaceExtension)
import Data.Char            (isSpace)
import Data.List            (isPrefixOf)

main     = getArgs >>= mapM txFile 

txFile f = (putStrLn . unlines . map txLine . lines) =<< readFile f

txLine l 
  | pfx `isPrefixOf` l = pfx
  | otherwise          = l
  where
    pfx                = "\\begin{code}"

