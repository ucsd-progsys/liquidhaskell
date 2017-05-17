-- | Progress Bar API
module Language.Fixpoint.Utils.Progress (
      withProgress
    , progressInit
    , progressTick
    , progressClose
    ) where

import           Control.Monad                    (when)
import           System.IO.Unsafe                 (unsafePerformIO)
import           System.Console.CmdArgs.Verbosity (isNormal)
import           Data.IORef


import           System.Console.AsciiProgress

{-# NOINLINE pbRef #-}
pbRef :: IORef (Maybe ProgressBar)
pbRef = unsafePerformIO (newIORef Nothing)

withProgress :: Int -> IO a -> IO a
withProgress n act = displayConsoleRegions $ do
  -- putStrLn $ "withProgress: " ++ show n
  progressInit n
  r <- act
  progressClose
  return r

progressInit :: Int -> IO ()
progressInit n = do
  normal <- isNormal 
  when normal $ do
    pr <- mkPB n
    writeIORef pbRef (Just pr)

mkPB   :: Int -> IO ProgressBar

mkPB n = newProgressBar def { pgWidth       = 80
                            , pgTotal       = toInteger n
                            , pgFormat      = "Working :percent [:bar]"
                            , pgPendingChar = '.'
                            , pgOnCompletion = Nothing -- Just "Done solving." --  :percent."
                            }

progressTick :: IO ()
progressTick    = go =<< readIORef pbRef
  where
   go (Just pr) = tick pr
   go _         = return ()

progressClose :: IO ()
progressClose = go =<< readIORef pbRef
  where
    go (Just p) = complete p
    go _        = return ()
