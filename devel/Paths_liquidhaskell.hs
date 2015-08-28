{-# LANGUAGE TemplateHaskell #-}
module Paths_liquidhaskell where

import Language.Haskell.TH
import System.Directory
import System.FilePath

getDataFileName :: FilePath -> IO FilePath
getDataFileName f = do
  let loc = $(do { loc <- location; f <- runIO (canonicalizePath (loc_filename loc)); litE (stringL f); })
  let root = takeDirectory (takeDirectory loc)
  return (root </> f)
