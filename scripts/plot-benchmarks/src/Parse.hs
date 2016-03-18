module Parse where

import Benchmark
import Data.Csv
import Data.List
import System.Directory
import Data.Either
import qualified Data.Vector as V
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Time.Clock.POSIX
import Data.Time.LocalTime
import System.FilePath

gulpLogs :: FilePath -> IO [V.Vector Benchmark]
gulpLogs f = do
   conts <- getDirectoryContents f
   let justCsv = filter (isSuffixOf ".csv") conts
   let noHidden = filter (\a -> not (isPrefixOf "." a)) justCsv
   let toGulp = fmap (\a -> f </> a) noHidden
   logs <- sequence $ fmap parseLog toGulp
   return $ rights logs

parseLog :: FilePath -> IO (Either String (V.Vector Benchmark))
parseLog p = do
   file <- BS.readFile p
   let (hdr, csv) = splitHeader file delimiter
   timezone <- getCurrentTimeZone
   case (getEpochTime hdr) of
      Nothing -> return $ Left "missing timestamp!"
      Just ts -> case (decode HasHeader csv) of
         Right bm ->
            return $ Right $ fmap
               (\a -> a {benchTimestamp = utcToLocalTime
                                             timezone
                                             $ posixSecondsToUTCTime
                                               $ realToFrac ts})
               bm

delimiter :: String
delimiter = take 80 $ repeat '-'

getEpochTime :: [String] -> Maybe Int
getEpochTime s = do
   elm <- find (isPrefixOf "Epoch Timestamp:") s
   elm' <- stripPrefix "Epoch Timestamp:" elm
   return (read elm' :: Int)

splitHeader :: BS.ByteString -> String -> ([String], BS.ByteString)
splitHeader msg delim = (hdr, BS.pack $ unlines csv)
   where
      (hdr, csv) = let ((hdrr, csvr), _) = foldl' foldFn initAcc lns in
         (reverse hdrr, reverse csvr)
      lns = lines $ BS.unpack msg
      initAcc = (([],[]), False)
      foldFn ((ls, rs), True) e = ((ls, e:rs), True)
      foldFn ((ls, rs), False) e = if e == delim
                                      then
                                      ((ls, rs), True)
                                      else
                                      ((e:ls, rs), False)

dumpLogs :: FilePath -> [(String, [(LocalTime, Benchmark)])] -> IO ()
dumpLogs out dps = sequence_ $ fmap dumpLog dps
   where
      dumpLog :: (String, [(LocalTime, Benchmark)]) -> IO ()
      dumpLog (n, dps') = do
         let n' = specToUscore n
         let dps'' = encodeByName
                        (V.fromList [csvOutName,
                                     csvOutDate,
                                     csvOutTime,
                                     csvOutPass])
                        dps'
         BS.writeFile (out </> n' ++ ".csv") dps''
      specToUscore s = fmap mapper s
         where
            mapper c = case c of
               '/' -> '_'
               '.' -> '_'
               c' -> c'
