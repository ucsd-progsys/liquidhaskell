{-# LANGUAGE TemplateHaskell #-}

module Paths_liquidhaskell where

import Language.Haskell.TH
import System.Directory
import System.FilePath
import Data.Version (Version, makeVersion)

getDataFileName :: FilePath -> IO FilePath
getDataFileName fp = do
  let loc' = $(do { loc <- location; f <- runIO (canonicalizePath (loc_filename loc)); litE (stringL f); })
  let root = takeDirectory (takeDirectory loc')
  return (root </> fp)

-- | dummy version (devel only)
version :: Version
version = makeVersion [0,0,0,0]