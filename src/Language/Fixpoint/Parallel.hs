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
import Language.Fixpoint.Config

import Debug.Trace
import Control.Exception

-- | A message to a worker thread
data ToWorker a =
   Execute (FInfo a) -- ^ A FInfo to solve
   | Die -- ^ An order to the worker to shut down

instance Show (ToWorker a) where
   show (Execute _) = "Execute"
   show (Die) = "Die"

-- | A response from a worker thread
data FromWorker a =
   Returned (Result a) -- ^ The Result of solving an FInfo
   | Dead -- ^ Confirmation that a thread has shut down

-- | Conains the nessesary channels to communicate with the worker threads
data Workers a =
   Workers
   {toWorker :: Chan (ToWorker a),
    fromWorker :: Chan (FromWorker a)}

-- | Start the worker threads, get the channels used to communicate with them
initWorkers :: Int -- ^ The number of threads to spawn
               -> (FInfo a -> IO (Result a)) -- ^ The action that the workers
               -- should execute
               -> IO (Maybe (Workers a)) -- ^ If the number of threads was
               -- greater than 0, returns a Workers, otherwise Nothing
initWorkers 0 _ = return Nothing
initWorkers c a = do
   tw <- newChan
   fw <- newChan
   let workers = Workers {toWorker = tw, fromWorker = fw}
   let actions = replicate (fromIntegral c) $ action tw fw
   mapM_ forkIO actions
   return $ Just workers
   where
      action tw fw = do
         input <- readChan tw
         traceIO $ "Entered action, read: " ++ show input
         case input of
            (Execute f) -> do
               output <- onException (a f) (traceIO "exception!")
               traceIO "Solve returned"
               writeChan fw (Returned output)
               action tw fw
            _ -> traceIO "Died" >> writeChan fw Dead

-- | Kill all worker threads
finalizeWorkers :: Int -- ^ The number of running threads
                   -> Workers a
                   -> IO () -- ^ If any solutions were pending, they are
                   -- discarded
finalizeWorkers c w = do
   writeList2Chan (toWorker w) (replicate (fromIntegral c) Die)
   goFW c
   where
      goFW 0 = return ()
      goFW c' = do
         curr <- readChan $ fromWorker w
         case curr of
            Dead -> goFW (c' - 1)
            _ -> goFW c'

-- | Solve a list of FInfos using the provided solver function in parallel
inParallelUsing :: Config
                   -> [FInfo a] -- ^ To solve in parallel
                   -> (FInfo a -> IO (Result a)) -- ^ The solver function
                   -> IO (Maybe (Result a)) -- ^ The combined results, or
                   -- Nothing on error
inParallelUsing c finfos a = do
   workers <- initWorkers (cores c) a
   case workers of
      Nothing -> return Nothing
      (Just workers') -> do
         traceIO $ "Solving "
            ++ show (length finfos)
            ++ " in parallel with "
            ++ show (cores c)
            ++ " threads..."
         writeList2Chan (toWorker workers') (map Execute finfos)
         traceIO "Sent FInfos to workers..."
         result <- waitForAll (length finfos) [] (fromWorker workers')
         finalizeWorkers (cores c) workers'
         return $ Just $ mconcat $ map (\(Returned r) -> r) result
   where
      waitForAll 0 o _ = sequence o
      waitForAll n o w = waitForAll (n - 1) (readChan w : o) w
