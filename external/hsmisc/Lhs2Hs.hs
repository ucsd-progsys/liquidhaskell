#!/usr/bin/env runhaskell

import System.Environment (getArgs)
import System.FilePath (replaceExtension)
import Data.Char        (isSpace)

main         = getArgs >>= mapM lhs2hsFile

lhs2hsFile f = do str <- readFile f
                  writeFile (replaceExtension f ".hs") $ lhs2hs str

lhs2hs       :: String -> String
lhs2hs       = unlines . stepFold step Comment . map trimSpaces . lines 
trimSpaces   = reverse . dropWhile isSpace . reverse 

data Mode = Code | Comment

step Comment "\\begin{code}" = (Code   , "")
step Comment ""              = (Comment, "")
step Comment s               = (Comment, "-- " ++ s)
step Code    "\\end{code}"   = (Comment, "")
step Code    s               = (Code   , s )

stepFold f b []     = []
stepFold f b (x:xs) = y : stepFold f b' xs 
                      where (b', y) = f b x 
