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

    -- * parallel solver function
    inParallelUsing

) where

import Control.Concurrent
import Language.Fixpoint.Types
import Control.Exception


-- | Throw an UnknownError exception
unknownError :: String -> Result a
unknownError e = Result (UnknownError e) mempty


-- | Solve a list of FInfos using the provided solver function in parallel
inParallelUsing :: [FInfo a] -- ^ To solve in parallel
                   -> (FInfo a -> IO (Result a)) -- ^ The solver function
                   -> IO (Result a) -- ^ The combined results
inParallelUsing finfos a = do
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
