-- | Progress Bar API

module Language.Fixpoint.Progress (
      progressInit
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

progressInit :: Int -> IO ()
progressInit n = do
  loud <- isLoud
  unless loud $ do
    pr <- mkPB n
    writeIORef pbRef (Just pr)

mkPB   :: Int -> IO ProgressBar
mkPB n = newProgressBar def { pgWidth = 80
                            , pgTotal = n
                            , pgFormat = "Working :percent [:bar]"
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
