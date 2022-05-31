{-# LANGUAGE OverloadedStrings #-}

module Main where

import Shelly ( readfile, shelly, writefile, (</>) )
import qualified Data.Text as T
import Data.Foldable (for_)

main :: IO ()
main = shelly $ do
  files <- fmap (\f -> ("../" :: String) </> T.unpack f) . T.lines <$> readfile "files_to_change.txt"
  for_ files $ \f -> do
    fContents <- readfile f
    writefile f $ "{-@ LIQUID \"--expect-any-error\" @-}\n" <> fContents

