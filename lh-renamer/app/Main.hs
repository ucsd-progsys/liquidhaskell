{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Main where

import Shelly
import Data.Function ((&))
import Data.Traversable (for)
import Data.Foldable (foldl')
import Control.Monad (void)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Char as C
import Debug.Trace (traceM)
import GHC.Stack
import System.Environment (getArgs)
default (T.Text)

main :: HasCallStack => IO ()
main = shelly $ do
  args <- liftIO $ getArgs
  hsFiles <- getHsFiles $ head args
  void $ for hsFiles $ \fp -> verbosely $ do
    (goodBaseName, goodName) <- getGoodName fp
    traceM goodName
    rnm <- renameModule goodBaseName fp
    rnm `seq` (mv fp goodName)

getHsFiles :: HasCallStack => FilePath -> Sh [FilePath]
getHsFiles = findWhen (pure . hasExt ".hs")

getGoodName :: HasCallStack => FilePath -> Sh (T.Text, FilePath)
getGoodName fp = do
  let (directory, baseName, extension) = nameSplit fp
      appendN gn = do
        exists <- test_e $ directory </> gn <.> extension
        if exists && (directory </> gn <.> extension) /= fp then go gn 0 else pure gn
          where
            go :: T.Text -> Int -> Sh T.Text
            go gn n = do
              exists <- test_e $ directory </> (gn <> T.pack (show n)) <.> extension
              if exists then go gn (succ n) else pure $ gn <> T.pack (show n)
      baseName' =
        baseName
        & T.map (\case
                    '-' -> '_'
                    '.' -> '_'
                    c -> c)
        & T.uncons
        & \case
          Nothing -> error "Empty basename!"
          Just (x, xs) -> C.toUpper x `T.cons` xs
  goodName <- appendN baseName'
  pure $ (goodName, directory </> goodName <.> extension)

nameSplit :: HasCallStack => FilePath -> (T.Text, T.Text, T.Text)
nameSplit fp =
  let (directory, fileName) = T.breakOnEnd "/" $ T.pack fp
      (baseName, extension) = T.breakOnEnd "." fileName
  in
    (T.init directory, T.init baseName, extension)

renameModule :: HasCallStack => T.Text -> FilePath -> Sh ()
renameModule goodName fp = do
  contents <- liftIO $ T.readFile fp
  let contents' =
        T.unlines $
        reverse $
        foldl' (\acc line ->
                   let line' = if "module " `T.isPrefixOf` line
                               then case getExportList line of
                                      Nothing -> "module " <> goodName <> " where"
                                      Just el -> "module " <> goodName <> " (" <> el <> ") where"
                               else line
                   in
                     line' : acc) [] $
        T.lines $
        contents
  liftIO $ T.writeFile fp contents'
  where
    getExportList line = let el = T.dropWhile (/= '(') . T.takeWhile (/= ')') $ line
      in if T.any (=='(') line then Just (T.tail el) else Nothing
