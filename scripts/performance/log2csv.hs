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
logFile = logLine `manyTill` endOfInput

logLine :: Parser (String, String)
logLine = do
   first <- anyChar `manyTill` (char ',')
   skipSpace
   second <- anyChar `manyTill` (char '`')
   anyChar `manyTill` endOfLine
   return (first, second)


main = do
   (i:_) <- getArgs
   logF <- return $ readLog $ BS.pack i
   case logF of
      Done _ r -> putStr $ printLog r
      _ -> exitFailure
