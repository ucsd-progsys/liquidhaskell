-- | Progress Bar API
module Language.Fixpoint.Utils.Progress (
      withProgress
    , progressInit
    , progressTick
    , progressClose
    ) where

import           Control.Monad                    (unless)
import           System.IO.Unsafe                 (unsafePerformIO)
import           System.Console.CmdArgs.Verbosity (isLoud)
import           Data.IORef


withProgress :: Int -> IO a -> IO a
withProgress _ x = x

progressInit :: Int -> IO ()
progressInit _ = return ()

progressTick :: IO ()
progressTick = return ()

progressClose :: IO ()
progressClose = return ()
