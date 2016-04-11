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
import Data.Colour ()
import Data.Colour.Names ()
import System.FilePath

fileOptions :: FileOptions
fileOptions = def-- (def {_fo_size = (1024, 768)} :: FileOptions)

lineColor1 :: AlphaColour Double
lineColor1 = withOpacity darkred 0.5

pointColor1 :: AlphaColour Double
pointColor1 = opaque red

lineColor2 :: AlphaColour Double
lineColor2 = withOpacity darkgreen 0.5

pointColor2 :: AlphaColour Double
pointColor2 = opaque green

plotData :: (Default r, ToRenderable r)
            => FilePath
            -> [(String, [(LocalTime, a)])]
            -> (String -> [(LocalTime, a)] -> EC r ())
            -> IO ()
plotData out dps with = sequence_ $ fmap plotDp dps
   where
      plotDp (n, dps') = do
         let n' = specToUscore n
         let options = fileOptions
         toFile options (out </> n' ++ ".svg") $ with n dps'
      specToUscore s = fmap mapper s
         where
            mapper c = case c of
               '/' -> '_'
               '.' -> '_'
               c' -> c'

plotCompareData :: (Default r, ToRenderable r)
                   => FilePath
                   -> [((String, [(LocalTime, a)]),(String, [(LocalTime, a)]))]
                   -> (String
                       -> String
                       -> ([(LocalTime, a)],[(LocalTime, a)]) -> EC r ())
                   -> IO ()
plotCompareData out dps with = sequence_ $ fmap plotDp dps
   where
      plotDp ((ln, ldps'), (rn, rdps')) = do
         let ln' = specToUscore ln
         let rn' = specToUscore rn
         let dps' = (ldps', rdps')
         let options = fileOptions
         toFile
            options
            (out </> ln' ++ "_vs_" ++ rn' ++ ".svg")
            $ with ln rn dps'
      specToUscore s = fmap mapper s
         where
            mapper c = case c of
               '/' -> '_'
               '.' -> '_'
               c' -> c'

plotCompareTimeData :: FilePath
                       -> [((String, [(LocalTime, Double)]),
                            (String, [(LocalTime, Double)]))]
                       -> IO ()
plotCompareTimeData out dps = plotCompareData out dps with
   where
      with ln rn (ldps, rdps) = do
         layoutlr_title .= ln ++ " vs. " ++ rn ++ " Times"
         setColors [lineColor1, lineColor2, pointColor1, pointColor2]
         setShapes [PointShapeCircle, PointShapeCircle]
         plotLeft $ line "" [ldps]
         plotRight $ line "" [rdps]
         plotLeft $ points ln ldps
         plotRight $ points rn rdps

plotTimeData :: FilePath -> [(String, [(LocalTime, Double)])] -> IO ()
plotTimeData out dps = plotData out dps with
   where
      with n' dps' = do
            layout_title .= n' ++ " Times"
            setColors [lineColor1, pointColor1]
            plot $ line "" [dps']
            plot $ points n' dps'

getCompareData :: ([Benchmark] -> [(LocalTime, a)])
                  -> FilePath
                  -> [(String, String)]
                  -> IO [((String, [(LocalTime, a)]),
                          (String, [(LocalTime, a)]))]
getCompareData mapper f bps = sequence $ fmap pairUp bps
   where
      pairUp (l, r) = do
         [l'] <- getData mapper f [l]
         [r'] <- getData mapper f [r]
         return (l', r')

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
getTimeData = getData timeDataMapper


getCompareTimeData :: FilePath
                   -> [(String, String)]
                   -> IO [((String, [(LocalTime, Double)]),
                           (String, [(LocalTime, Double)]))]
getCompareTimeData = getCompareData timeDataMapper

timeDataMapper :: [Benchmark] -> [(LocalTime, Double)]
timeDataMapper bs' = [(benchTimestamp x, benchTime x) | x <- bs' ]



getSuccessData :: FilePath -> [String] -> IO [(String, [(LocalTime, Bool)])]
getSuccessData = getData mapper
   where
      mapper bs' = [(benchTimestamp x, benchPass x) | x <- bs' ]

plotSuccessData :: FilePath -> [(String, [(LocalTime, Bool)])] -> IO ()
plotSuccessData out dps = plotData out dps with
   where
      dps'' v = fmap (\(l, r) -> case r of
                                  True -> (l, (1 :: Integer))
                                  False -> (l, 0)) v
      with n' dps' = do
         layout_title .= n' ++ " Test Result"
         plot (line n' [dps'' dps'])

getAllData :: FilePath -> [String] -> IO [(String, [(LocalTime, Benchmark)])]
getAllData = getData mapper
   where
      mapper bs' = [(benchTimestamp x, x) | x <- bs']
