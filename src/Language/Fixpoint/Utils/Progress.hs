-- | Progress Bar API

module Language.Fixpoint.Utils.Progress (
      withProgress
    , progressInit
    , progressTick
    , progressClose
    ) where

import           Control.Monad                    (unless)
import           System.IO.Unsafe                 (unsafePerformIO)
import           System.Console.CmdArgs.Verbosity (isLoud, whenLoud)
import           Data.IORef
import           System.Console.AsciiProgress -- (ProgressBar(..), Options(..), isComplete, def, newProgressBar, tick)

{-# NOINLINE pbRef #-}
pbRef :: IORef (Maybe ProgressBar)
pbRef = unsafePerformIO (newIORef Nothing)

withProgress :: Int -> IO a -> IO a
withProgress n act = displayConsoleRegions $ do
  progressInit n
  r <- act
  progressClose
  return r

progressInit :: Int -> IO ()
progressInit n = do
  loud <- isLoud
  -- putStrLn $ "progressInit: loud = " ++ show loud
  unless loud $ do
    pr <- mkPB n
    writeIORef pbRef (Just pr)

mkPB   :: Int -> IO ProgressBar

mkPB n = newProgressBar def { pgWidth       = 80 
                            , pgTotal       = toInteger n
                            , pgFormat      = "Working :percent [:bar]"
                            , pgPendingChar = '.'
                            , pgOnCompletion = Just "Done solving." --  :percent."
                            }

{-
mkPB n = newProgressBar def { pgWidth = 100
                            , pgOnCompletion = Just "Done :percent after :elapsed seconds"
                            }
 -}

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
