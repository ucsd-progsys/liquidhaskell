{-# LANGUAGE BangPatterns  #-}

module Gradual.Log (
  logDepth, logSpans, logCand, logSens, logLocal, logSpec, logParts, logGParts
  , logConcr, logSol, logMatches,
  printLog
) where

import Language.Fixpoint.Types
import Gradual.Types
import Gradual.PrettyPrinting


import Data.IORef
import System.IO.Unsafe

import Data.Maybe (fromMaybe)
import qualified Data.List as L 
import qualified Data.HashMap.Strict as M

logDepth :: Int -> IO () 
logDepth d  = modifyIORef logRef $ \lg -> lg{lDepth = d}

logSpans :: GSpan -> IO () 
logSpans gp = modifyIORef logRef $ \lg -> lg{lSpans = gp}

logCand :: Pretty a => KVar -> [a] -> IO ()
logCand k !xs = do 
  putStrLn ("Candidates for " ++ show k ++ ":\n" ++ pretty xs)
  -- putStrLn ("Candidates for " ++ show k ++ ":" ++ show (length xs))
  modifyIORef logRef $ \lg -> lg{lCands = (k,length xs):lCands lg}

logSens ::  Pretty a => KVar -> [a] -> IO () 
logSens k !xs = do 
  putStrLn ("Sensible for " ++ show k ++ ":\n" ++ pretty xs)
  -- putStrLn ("Sensible for " ++ show k ++ ":" ++ show (length xs))
  modifyIORef logRef $ \lg -> lg{lSense = (k,length xs):lSense lg}

logLocal :: Pretty a => KVar -> [a] -> IO () 
logLocal k !xs = do 
  -- putStrLn ("Local for " ++ show k ++ ":" ++ pretty xs)
  -- putStrLn ("Local for " ++ show k ++ ":" ++ show (length xs))
  modifyIORef logRef $ \lg -> lg{lLocal = (k,length xs):lLocal lg}

logSpec :: Pretty a => KVar -> [a] -> IO () 
logSpec k !xs = do 
  putStrLn ("Presice for " ++ show k ++ ":\n" ++ pretty xs)
  -- putStrLn ("Pres for " ++ show k ++ ":" ++ show (length xs))
  modifyIORef logRef $ \lg -> lg{lPrecise = (k,length xs):lPrecise lg}


logGParts :: [a] -> IO ()
logGParts !xs = modifyIORef logRef $ \lg -> lg{lGParts = length xs}

logParts :: [a] -> IO [a] 
logParts !xs = do 
  modifyIORef logRef $ \lg -> lg{lParts = length xs}
  return xs 

logConcr :: [a] -> IO [a] 
logConcr !xs = do 
  modifyIORef logRef $ \lg -> lg{lConcrs = (lConcrs lg) ++ [length xs]}
  return xs 


logSol :: [a] -> IO ()
logSol !xs = modifyIORef logRef $ \lg -> lg{lSols = (lSols lg) ++ [length xs]}



logMatches :: [GSub ()] -> IO () 
logMatches gm = modifyIORef logRef $ \lg -> lg{lStatic = gm}


data Log = Log
  { lDepth   :: Int   -- gradual Depth Parameter
  , lSpans   :: GSpan -- How many times each occures 
  , lCands   :: [(KVar, Int)] -- How many candidates per occurence
  , lLocal   :: [(KVar, Int)] -- How many of these candidates are local 
  , lSense   :: [(KVar, Int)] -- How many of these candidates are sensible 
  , lPrecise :: [(KVar, Int)] -- How many of these candidates are precise
  , lParts   :: Int     -- Number of Partitions
  , lGParts  :: Int     -- Number of Partitions
  , lConcrs  :: [Int]   -- Number of Concretizations Per Partition
  , lSols    :: [Int]   -- Number of Solutions Per Partition
  , lStatic  :: [GSub ()] -- Static Solutions
  }

defLog :: Log 
defLog = Log 1 mempty [][][][] 1 0 [] [] mempty

logRef :: IORef Log
logRef = unsafePerformIO $ newIORef defLog


data Ints = Same Int | Diff [Int]

toInts :: [Int] -> Ints
toInts []  = Diff []
toInts [x] = Diff [x]
toInts (x:xs) = if all (==x) xs then Same x else Diff (x:xs) 


newtype MInts = MInts (Int, Ints) 


_toMaxInts :: Int -> [Int] -> MInts
_toMaxInts m []  = MInts (m, Diff [])
_toMaxInts m [x] = MInts (m, Diff [x])
_toMaxInts m (x:xs) = if all (==x) xs then MInts (m, Same x) else MInts (m, Diff (x:xs))

instance Show Ints where
  show (Same i)  = show i ++ "*"
  show (Diff is) = show is 

instance Show MInts where
  show (MInts (m, Same i))  = showMInt m i ++ "*"
  show (MInts (m, Diff is)) = "[" ++ L.intercalate "," (map (showMInt m) is) ++ "]"

showMInt :: Int -> Int -> String
showMInt m i = if i > m then (">"++show m) else show i



printLog :: IO () 
printLog = do 
  lg <- readIORef logRef
  let spans = lSpans lg 
  let gs    = reverse $ L.sort $ M.keys spans
  let occs  = map (makeOcc spans) gs
  putStrLn ("\nDepth\t #?  |  Occs\tCands\t Sens\t Local\t Prec  |  "
           ++ "Parts\t #γ\t SCs \t" ++  take (length (show (toInts $ lSols lg)) -4)  (repeat ' ') ++ " Sols \n")
  putElems [ show $ lDepth lg
           , show (length gs)
           , show (map length occs) 
           , show (map (toInts . map (\k -> fromMaybe 0 (L.lookup k (lCands lg)))) occs) 
           , show (map (toInts . map (\k -> fromMaybe 0 (L.lookup k (lSense lg)))) occs) 
           , show (map (toInts . map (\k -> fromMaybe 0 (L.lookup k (lLocal lg)))) occs) 
           , show (map (toInts . map (\k -> fromMaybe 0 (L.lookup k (lPrecise lg)))) occs) 
           , (show $ lGParts lg) ++ "/" ++ (show $ lParts lg)
           , show (toInts $ lConcrs lg)
           , show (toInts $ lSols lg)
           , show (length $ lStatic lg)
           ]



makeOcc :: GSpan -> KVar -> [KVar]
makeOcc spans k = 
  map fst $ 
  reverse $ 
  L.sortBy (\x y -> compare (snd x) (snd y)) $ 
  M.lookupDefault [] k spans

putElems :: [String] -> IO ()
putElems = putStrLn . L.intercalate " &\t"

