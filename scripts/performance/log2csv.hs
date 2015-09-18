import Data.Attoparsec

type Log = [(String, String)]

printLog :: Log -> String
printLog l = printLines $ fmap printLine l
   where
      printLines :: [String] -> String
      printLines = concat
      printLine :: (String, String) -> String
      printLine (test, time) = test ++ ";" ++ time ++ "\n"

main = undefined
