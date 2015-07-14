module Language.Fixpoint.Parallel (

    -- * parallel solver function
    inParallelUsing

    -- * Determine the number of threads specified by the config
  , threadCount

) where

import Control.Concurrent
import Language.Fixpoint.Types
import Language.Fixpoint.Config

data ToWorker a =
   Execute (FInfo a) -- ^ A FInfo to solve
   | Die -- ^ An order to the worker to shut down

data FromWorker a =
   Returned (Result a) -- ^ The Result of solving an FInfo
   | Dead -- ^ Confirmation that a thread has shut down

data Workers a =
   Workers
   {toWorker :: Chan (ToWorker a),
    fromWorker :: Chan (FromWorker a)}

-- | Get the number of threads specified by the config
threadCount :: Config
               -> Word -- ^ The number of threads, with 0 indicating serial
threadCount c =
   case cores c of
      Cores n -> n

-- | Start the worker threads, get the channels used to communicate with them
initWorkers :: Word -- ^ The number of threads to spawn
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
         case input of
            (Execute f) -> do
               output <- a f
               writeChan fw (Returned output)
               action tw fw
            _ -> writeChan fw Dead

-- | Kill all worker threads
finalizeWorkers :: Word -- ^ The number of running threads
                   -> Workers a
                   -> IO () -- ^ If any solutions were pending, they are
                   -- discarded
finalizeWorkers c w = goFW c
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
   workers <- initWorkers (threadCount c) a
   case workers of
      Nothing -> return Nothing
      (Just workers') -> do
         writeList2Chan (toWorker workers') (map Execute finfos)
         result <- waitForAll (length finfos) [] (fromWorker workers')
         finalizeWorkers (threadCount c) workers'
         return $ Just $ mconcat $ map (\(Returned r) -> r) result
   where
      waitForAll 0 o _ = sequence o
      waitForAll n o w = waitForAll (n - 1) (readChan w : o) w
