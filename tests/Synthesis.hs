{-# LANGUAGE TupleSections #-}

module Main where

import           Test.Tasty 
import           Test.Tasty.HUnit

import qualified Data.Text    as T
import qualified Data.Text.IO as T
import           System.FilePath
import           System.Process
import           System.IO
import           System.Directory
import           System.Exit
import           System.IO.Unsafe
import           Data.Tuple.Extra

-------------------------------------------------------------
-- | Contains the input files
-------------------------------------------------------------
synthesisTestsDir :: FilePath
synthesisTestsDir = "tests/synthesis/tests"
-------------------------------------------------------------

-------------------------------------------------------------
-- | Contains the results of the synthesis on the inputs
-------------------------------------------------------------
logDir :: FilePath
logDir = "tests/synthesis/logs"
-------------------------------------------------------------

-------------------------------------------------------------
-- | Contains the outputs that we need to check logs against
-------------------------------------------------------------
outputsDir :: FilePath
outputsDir = "tests/synthesis/static"
-------------------------------------------------------------

main :: IO ()
main = do 
    print " Synthesis test suite "
    result <- fromInput
    defaultMain (tests result)

fromInput :: IO [(FilePath, T.Text, [[T.Text]])]
fromInput = do
    res <- createLogs -- Get the filename from here
    logs <- handleLogs (map thd3 res)
    let filenames = map fst3 res
        programNames = map (head . T.words . head . head) logs 
        result = zip3 filenames programNames logs
    return result

handleLogs :: [T.Text] -> IO [[[T.Text]]]
handleLogs texts 
    = return (map handleLog texts)

keyword :: T.Text
keyword = T.pack " Hole Fills:"

startsWith :: T.Text -> T.Text -> Bool
startsWith kw line = T.isPrefixOf kw line

-- | @walkFile@ returns empty means that there is no solution produced 
--              for given specification (needs to be checked)

walkFile :: T.Text -> [T.Text]
walkFile text = dropWhile (not . startsWith keyword) ls
    where ls = T.lines text 

-- | Lines from the solution in the log file (without trailing characters)
handleLog :: T.Text -> [[T.Text]]
handleLog text =
    let toBeParsed = walkFile text
        sols = T.splitOn (T.pack delim) (T.unlines (tail toBeParsed))
        noTrailing = map (filter (not . T.null)) (map (map T.strip) (map T.lines sols))
    in  noTrailing


delim :: String
delim = "*********************************************"


createLogs :: IO [(FilePath, ExitCode, T.Text)]
createLogs = do 
    files <- listDirectory synthesisTestsDir
    let testFiles = filter (\x -> takeExtension x == ".hs") files
    res <- mapM runLiquid testFiles
    let (ecs, ts) = unzip res
        fs = map dropExtension testFiles
    return (zip3 fs ecs ts)

runLiquid :: FilePath -> IO (ExitCode, T.Text)
runLiquid tgt = do
    let inFile = synthesisTestsDir </> tgt
        log'   = logDir </> (dropExtension tgt <.> ".log")
    -- use `liquid` if its on the path, otherwise use stack to call it
    bin <- maybe "stack exec -- liquid"
        ( <> " --ghc-option=-hide-package=base"
          <> " --ghc-option=-hide-package=containers"
        ) <$> findExecutable "liquid"
    withFile log' WriteMode $ \h -> do
        (_, _, _, ph) <- createProcess $ (shell (bin ++ ' ' : inFile)) { std_out = UseHandle h, std_err = UseHandle h }
        exitCode      <- waitForProcess ph
        (exitCode, ) <$> T.readFile log'


getSolutions :: FilePath -> IO T.Text
getSolutions tgt = do
    let file = outputsDir </> tgt
    T.readFile file
    
mkTgt :: FilePath -> FilePath
mkTgt t = addExtension t ".hs"



-- | Get solution from outputs line by line in order to compare
lineFile :: T.Text -> T.Text -> [T.Text]
lineFile progName file = 
    dropWhile (\x -> not (startsWith (progName `T.append` (T.pack " ")) x) || 
                     startsWith (progName `T.append` (T.pack " ::")) x) (T.lines file)

clean :: [T.Text] -> [T.Text]
clean ls = filter (not . T.null) (map T.strip ls)

processAnswers :: [(FilePath, T.Text, [[T.Text]])] -> [(FilePath, [[T.Text]], [T.Text])]
processAnswers = map processAnswer 

processAnswer :: (FilePath, T.Text, [[T.Text]]) -> (FilePath, [[T.Text]], [T.Text])
processAnswer (fp, prog, ts) = 
    let file = unsafePerformIO (getSolutions (mkTgt fp))
        fileLines = lineFile prog file
        cleanLines = clean fileLines
    in  (fp, ts, cleanLines) 

compareLines :: [T.Text] -> [T.Text] -> Bool
compareLines [] [] = True
compareLines (t:ts) (l:ls) = t == l && compareLines ts ls
compareLines _ _ = False

buildTestCase :: (FilePath, [[T.Text]], [T.Text]) -> TestTree
buildTestCase (fp, ls, ts) 
    = testCase 
        fp 
        ((foldr (\l b -> compareLines ts l || b) False ls) @?= True)

tests :: [(FilePath, T.Text, [[T.Text]])] -> TestTree
tests inputs = 
    let answers = processAnswers inputs
        units   = map buildTestCase answers
    in  testGroup " Tests for synthesis " units

