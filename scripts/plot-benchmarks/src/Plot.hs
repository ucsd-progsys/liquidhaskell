{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Plot where

import Benchmark
import Parse
import qualified Data.Map as Map
import Data.Foldable
import Data.List
import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Diagrams
import Data.Time.LocalTime

plotData :: (Default r, ToRenderable r)
            => [(String, [(LocalTime, a)])]
            -> (String -> [(LocalTime, a)] -> EC r ())
            -> IO ()
plotData dps with = sequence_ $ fmap plotDp dps
   where
      plotDp (n, dps') = do
         let n' = specToUscore n
         let options = (def :: FileOptions)
         toFile options (n' ++ ".svg") $ with n dps'
      specToUscore s = fmap mapper s
         where
            mapper c = case c of
               '/' -> '_'
               '.' -> '_'
               c' -> c'

plotCompareData :: (Default r, ToRenderable r)
                   => [((String, [(LocalTime, a)]),(String, [(LocalTime, a)]))]
                   -> (String -> ([(LocalTime, a)],[(LocalTime, a)]) -> EC r ())
                   -> IO ()
plotCompareData dps with = sequence_ $ fmap plotDp dps
   where
      plotDp ((ln, ldps'), (rn, rdps')) = do
         let ln' = specToUscore ln
         let rn' = specToUscore rn
         let n = ln ++ " vs " ++ rn
         let dps' = (ldps', rdps')
         let options = (def :: FileOptions)
         toFile options (ln' ++ "_vs_" ++ rn' ++ ".svg") $ with n dps'
      specToUscore s = fmap mapper s
         where
            mapper c = case c of
               '/' -> '_'
               '.' -> '_'
               c' -> c'

--plotCompareTimeData :: ((String, [(Int, Double)]), (String, [(Int, Double)]))
--                       -> IO ()
{-
plotCompareTimeData dps = plotCompareData dps with
   where
      with :: String -> ([(Int, a)], [(Int, a)]) -> EC r ()
      with n' (ldps, rdps) = do
         layoutlr_title .= n' ++ " Times"
         plotLeft (line n' [ldps])
         plotRight (line n' [rdps])-}

plotTimeData :: [(String, [(LocalTime, Double)])] -> IO ()
plotTimeData dps = plotData dps with
   where
      with n' dps' = do
            layout_title .= n' ++ " Times"
            plot (line n' [dps'])

plotSuccessData :: [(String, [(LocalTime, Bool)])] -> IO ()
plotSuccessData dps = plotData dps with
   where
      dps'' v = fmap (\(l, r) -> case r of
                                  True -> (l, (1 :: Integer))
                                  False -> (l, 0)) v
      with n' dps' = do
         layout_title .= n' ++ " Test Result"
         plot (line n' [dps'' dps'])

getData :: ([Benchmark] -> [(LocalTime, a)])
                -> FilePath
                -> [String]
                -> IO [(String, [(LocalTime, a)])]
getData mapper f bs = do
   logs <- gulpLogs f
   let logMaps = fmap toBenchMap logs
   let combined = foldl' unionAppend Map.empty logMaps
   let onlyBs = Map.filterWithKey (\k _ -> k `elem` bs) combined
   let dataPs = Map.toList $ fmap mapper onlyBs
   let sorted =  fmap sortMapper dataPs
   return sorted
   where
      comparator (tsl, _) (tsr, _) = compare tsl tsr
      sortMapper (name, dps) = (name, sortBy comparator dps)

getTimeData :: FilePath -> [String] -> IO [(String, [(LocalTime, Double)])]
getTimeData = getData mapper
   where
      mapper bs' = [(benchTimestamp x, benchTime x) | x <- bs' ]

getSuccessData :: FilePath -> [String] -> IO [(String, [(LocalTime, Bool)])]
getSuccessData = getData mapper
   where
      mapper bs' = [(benchTimestamp x, benchPass x) | x <- bs' ]
