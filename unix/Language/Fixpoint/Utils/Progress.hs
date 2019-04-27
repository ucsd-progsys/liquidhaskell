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
mkPB n = newProgressBar def 
  { pgWidth       = 80
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

{- 
incTick :: ProgressBar -> IO () 
incTick pb = do
  st <- getProgressStats pb 
  if (incomplete st) 
    then putStrLn (show (stPercent st, stTotal st, stCompleted st)) >> (tick pb)
    else return () 

incomplete :: Stats -> Bool 
incomplete st = stPercent st < 100 -- stCompleted st < stTotal st
-}

progressClose :: IO ()
progressClose = go =<< readIORef pbRef
  where
    go (Just p) = complete p
    go _        = return ()
