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
    inParallelUsing'

) where

import Control.Concurrent
import Language.Fixpoint.Types
import Language.Fixpoint.Config
import Language.Fixpoint.Errors

import Debug.Trace
import qualified Data.HashMap.Strict as M

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
   | Threw String-- ^ Thread died because of an exception

-- | Conains the nessesary channels to communicate with the worker threads
data Workers a =
   Workers
   {to :: Chan (ToWorker a),
    from :: Chan (FromWorker a)}

unknownError :: String -> Result a
unknownError e = Result (UnknownError e) mempty

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
   let workers = Workers {to = tw, from = fw}
   let actions = replicate (fromIntegral c) $ action tw fw
   let forkFn (Left e) = traceIO ("Premature thread death! " ++ displayException (e :: SomeException))
       forkFn (Right _) = traceIO "Expected thread death!"
   mapM_ (`forkFinally` forkFn) actions
   return $ Just workers
   where
      action tw fw = do
         input <- readChan tw
         traceIO $ "Entered action, read: " ++ show input
         case input of
            (Execute f) -> do
               let handler (SomeException e) = do
                      traceIO $ "Thread caught exception!" ++ (displayException e)
                      return $ unknownError $ displayException e
               output <- catch
                         (do
                             traceIO $ "Size of SubC Map: " ++ (show $ M.size $ cm f)
                             a f)
                         handler
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
   writeList2Chan (to w) (replicate (fromIntegral c) Die)
   goFW c
   where
      goFW 0 = return ()
      goFW c' = do
         curr <- readChan $ from w
         case curr of
            Dead -> goFW (c' - 1)
            _ -> goFW c'

-- | Solve a list of FInfos using the provided solver function in parallel
inParallelUsing :: Int
                   -> [FInfo a] -- ^ To solve in parallel
                   -> (FInfo a -> IO (Result a)) -- ^ The solver function
                   -> IO (Result a) -- ^ The combined results, or
                   -- Nothing on error
inParallelUsing c finfos a = do
   workers <- initWorkers c a
   case workers of
      Nothing -> fail "Failed to create worker threads!"
      (Just workers') -> do
         traceIO $ "Solving "
            ++ show (length finfos)
            ++ " in parallel with "
            ++ show c
            ++ " threads..."
         writeList2Chan (to workers') (map Execute finfos)
         traceIO "Sent FInfos to workers..."
         result <- waitForAll (length finfos) [] (from workers')
         finalizeWorkers c workers'
         return $ mconcat $ map (\(Returned r) -> r) result
   where
      waitForAll 0 o _ = sequence o
      waitForAll n o w = waitForAll (n - 1) (readChan w : o) w

-- | Solve a list of FInfos using the provided solver function in parallel
inParallelUsing' :: [FInfo a] -- ^ To solve in parallel
                    -> (FInfo a -> IO (Result a)) -- ^ The solver function
                    -> IO (Result a) -- ^ The combined results, or
                    -- Nothing on error
inParallelUsing' finfos a = do
   fw <- newChan
   let action i = do
          let handler (SomeException e) = do
                 traceIO $ "Thread caught exception!" ++ (displayException e)
                 return $ unknownError $ displayException e
          o <- catch (traceIO ("Solving file: " ++ fileName i) >> a i) handler
          fw `writeChan` o
   mapM_ (forkIO . action) finfos
   result <- waitForAll (length finfos) [] fw
   return $ mconcat result
   where
      waitForAll 0 o _ = sequence o
      waitForAll n o w = waitForAll (n - 1) (readChan w : o) w
