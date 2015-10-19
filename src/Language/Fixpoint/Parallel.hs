{-# LANGUAGE CPP #-}

{-|
Module      : Language.Fixpoint.Parallel
Description : Parallel constraint solving
Copyright   : (c) Ranjit Jhala 2013-2014
License     : BSD3
Maintainer  : jhala@cs.ucsd.edu

The purpose of this module is to faciliate solving constraints in parallel. This
module exports @inParallelUsing@ which will solve a list of constraints in
parallel using the provided solving function
-}

module Language.Fixpoint.Parallel (
    inParallelUsing
  ) where

import Control.Concurrent
import Control.Concurrent.Async
import Language.Fixpoint.Types
import Control.Exception

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid
#endif

-- | Throw an UnknownError exception
unknownError :: String -> Result a
unknownError e = Result (UnknownError e) mempty

#if __GLASGOW_HASKELL__ < 710
displayException :: SomeException -> String
displayException = show
#endif

{- OLD
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
inParallelUsing :: (a -> IO (Result b)) -> [a] -> IO (Result b)
-------------------------------------------------------------------------------
inParallelUsing a finfos = do
   setNumCapabilities (length finfos)
   fw <- newChan
   let action i = do
          let handler e =
                 return $ unknownError $ displayException (e :: SomeException)
          o <- catch (a i) handler
          fw `writeChan` o
   mapM_ (forkIO . action) finfos
   result <- waitForAll (length finfos) [] fw
   return $ mconcat result
   where
      waitForAll 0 o _ = sequence o
      waitForAll n o w = waitForAll (n - 1) (readChan w : o) w
-}

-------------------------------------------------------------------------------
-- | Solve a list of FInfos using the provided solver function in parallel
-------------------------------------------------------------------------------
inParallelUsing :: (a -> IO (Result b)) -> [a] -> IO (Result b)
-------------------------------------------------------------------------------
inParallelUsing f xs = do
   setNumCapabilities (length xs)
   rs <- asyncMapM f xs
   return $ mconcat rs

asyncMapM :: (a -> IO b) -> [a] -> IO [b]
asyncMapM f xs = mapM (async . f) xs >>= mapM wait

{-
newtype Async a = Async (MVar a)

async :: IO a -> IO (Async a)
async action = do
  m <- newEmptyMVar
  forkIO $ putMVar m =<< action
  return (Async m)

wait :: Async a -> IO a
wait (Async m) = readMVar m

-}
