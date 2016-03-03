module Main where

import Plot
import Config

main :: IO ()
main = do
   conf <- getConfig
   timeData <- getTimeData (logDir conf) (plot conf)
   plotTimeData (outputDir conf) timeData
   compareTimeData <- getCompareTimeData (logDir conf) (plotCompare conf)
   plotCompareTimeData (outputDir conf) compareTimeData
