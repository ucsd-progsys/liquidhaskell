module Main where

import Plot
import Config
import Parse

main :: IO ()
main = do
   conf <- getConfig
   case (outputType conf) of
      Csv -> do
         csvData <- getAllData
                       (logDir conf)
                       (plot conf)
         dumpLogs
            (outputDir conf)
            csvData
      Svg -> do
         timeData <- getTimeData
                        (logDir conf)
                        (plot conf)
         plotTimeData
            (outputDir conf)
            timeData
         compareTimeData <- getCompareTimeData
                               (logDir conf)
                               (plotCompare conf)
         plotCompareTimeData
            (outputDir conf)
            compareTimeData
