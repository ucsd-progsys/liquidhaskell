import Data.Attoparsec.ByteString
import Data.Attoparsec.ByteString.Char8
import qualified Data.ByteString.Char8 as BS
import System.Environment
import System.Exit

type Log = [(String, String)]

printLog :: Log -> String
printLog l = printLines $ fmap printLine l
   where
      printLines :: [String] -> String
      printLines = concat
      printLine :: (String, String) -> String
      printLine (test, time) = test ++ ";" ++ time ++ "\n"

readLog :: BS.ByteString -> IResult BS.ByteString Log
readLog l = parse logFile l

logFile :: Parser Log
logFile = do
   anyChar `manyTill` endOfLine
   logLine `manyTill` endOfInput

logLine :: Parser (String, String)
logLine = do
   first <- anyChar `manyTill` (char ',')
   skipSpace
   second <- anyChar `manyTill` (char ',')
   anyChar `manyTill` endOfLine
   return (first, second)


main = do
   (i:_) <- getArgs
   i' <- BS.readFile i
   logF <- return $ readLog i'
   case (untilDone logF) of
      Right r -> putStr $ printLog $ r
      Left _ -> exitFailure
   where
      untilDone (Done _ r) = Right r
      untilDone (Partial f) = untilDone (f $ BS.pack "")
      untilDone failure = Left $ show failure
