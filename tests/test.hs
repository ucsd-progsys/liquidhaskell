{-# LANGUAGE CPP  #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DoAndIfThenElse     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Function (on)
import Control.Applicative
import qualified Control.Concurrent.STM as STM
import qualified Control.Monad.State as State
import Control.Monad.Trans.Class (lift)
import Control.Monad (when)
import Data.Char
import qualified Data.Functor.Compose as Functor
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.List as L 
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum(..), (<>))
import Data.Proxy
import Data.String
import Data.Tagged
import Data.Typeable
-- import Data.List (sort, reverse)
import qualified Data.Text    as T
import qualified Data.Text.IO as T
import Options.Applicative
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.IO.Error
import System.Process
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.Rerun
import Test.Tasty.Options
import Test.Tasty.Runners
import Test.Tasty.Runners.AntXML
import Paths_liquidhaskell

import Text.Printf

testRunner :: Ingredient
testRunner = rerunningTests
               [ listingTests
               , combineReporters myConsoleReporter antXMLRunner
               , myConsoleReporter
               ]

myConsoleReporter :: Ingredient
myConsoleReporter = combineReporters consoleTestReporter loggingTestReporter

main :: IO ()
main = do unsetEnv "LIQUIDHASKELL_OPTS"
          -- We don't run tests in depedency order, so having stale
          -- .liquid/ *.hs.bspec files can causes problems.
          -- system "rm -r tests/pos/.liquid/"
          -- system "rm -r tests/neg/.liquid/"
          run =<< tests
  where
    run   = defaultMainWithIngredients [
                testRunner
              , includingOptions [ Option (Proxy :: Proxy NumThreads)
                                 , Option (Proxy :: Proxy LiquidOpts)
                                 , Option (Proxy :: Proxy SmtSolver) ]
              ]
    tests = group "Tests" $ microTests  :
                            errorTests  : 
                            macroTests  :
                            proverTests :
                            benchTests  : 
                            []
                           

    -- tests = group "Tests" [ unitTests  ]
    -- tests = group "Tests" [ benchTests ]
    -- tests = group "Tests" [ selfTests  ]
    -- tests = group "Tests" [ errorTests ]

data SmtSolver = Z3 | CVC4 deriving (Show, Read, Eq, Ord, Typeable)

instance IsOption SmtSolver where
  defaultValue = Z3
  parseValue = safeRead . map toUpper
  optionName = return "smtsolver"
  optionHelp = return "Use this SMT solver"
  optionCLParser =
    option (fmap (read . map toUpper) str)
      (  long (untag (optionName :: Tagged SmtSolver String))
      <> help (untag (optionHelp :: Tagged SmtSolver String))
      )

newtype LiquidOpts = LO String deriving (Show, Read, Eq, Ord, Typeable, IsString)

instance Semigroup LiquidOpts where
  (LO "") <> y       = y
  x       <> (LO "") = x
  (LO x)  <> (LO y)  = LO $ x ++ (' ' : y)

instance Monoid LiquidOpts where
  mempty = LO ""
  mappend = (<>)

instance IsOption LiquidOpts where
  defaultValue = LO ""
  parseValue = Just . LO
  optionName = return "liquid-opts"
  optionHelp = return "Extra options to pass to LiquidHaskell"
  optionCLParser =
    option (fmap LO str)
      (  long (untag (optionName :: Tagged LiquidOpts String))
      <> help (untag (optionHelp :: Tagged LiquidOpts String))
      )

errorTests :: IO TestTree
errorTests = group "Error-Messages"
  [ 
    -- errorTest "tests/errors/ExportMeasure0.hs"      2 "Cannot lift `llen` into refinement logic"
    -- errorTest "tests/errors/ExportReflect0.hs"      2 "Cannot lift `identity` into refinement logic"
    -- errorTest "tests/errors/ExportMeasure1.hs"      2 "Cannot lift `psnd` into refinement logic"
    -- , errorTest "tests/errors/ShadowMeasureVar.hs"    2 "Multiple specifications for `shadow`"
    -- , errorTest "tests/errors/AmbiguousReflect.hs"    2 "Ambiguous specification symbol `mappend`"
    -- , errorTest "tests/errors/AmbiguousInline.hs"     2 "Ambiguous specification symbol `min`"
    -- , errorTest "tests/errors/MissingAbsRefArgs.hs"   2 "Illegal type specification for `Fixme.bar`"

    errorTest "tests/errors/ShadowFieldInline.hs"   2 "Error: Multiple specifications for `pig`"
  , errorTest "tests/errors/ShadowFieldReflect.hs"  2 "Error: Multiple specifications for `pig`"
  , errorTest "tests/errors/MultiRecSels.hs"        2 "Duplicated definitions for field `left`" 
  , errorTest "tests/errors/DupFunSigs.hs"          2 "Multiple specifications for `Main.fromWeekDayNum`"
  , errorTest "tests/errors/DupMeasure.hs"          2 "Error: Multiple specifications for `lenA`"
  , errorTest "tests/errors/ShadowMeasure.hs"       2 "Multiple specifications for `shadow`"
  , errorTest "tests/errors/DupData.hs"             2 "Multiple specifications for `OVec`"
  , errorTest "tests/errors/EmptyData.hs"           2 "one or more fields in the data declaration for `A`"
  , errorTest "tests/errors/BadGADT.hs"             2 "Error: Specified type does not refine Haskell type for `Main.Nil2`" 
  , errorTest "tests/errors/TerminationExprSort.hs" 2 "Illegal termination specification for `TerminationExpr.showSep`"
  , errorTest "tests/errors/TerminationExprNum.hs"  2 "Illegal termination specification for `TerminationExpr.showSep`"
  , errorTest "tests/errors/TerminationExprUnb.hs"  2 "Illegal termination specification for `go`"
  , errorTest "tests/errors/UnboundVarInSpec.hs"    2 "Illegal type specification for `Fixme.foo`"
  , errorTest "tests/errors/UnboundVarInAssume.hs"  2 "Illegal type specification for `Assume.incr`"
  , errorTest "tests/errors/UnboundCheckVar.hs"     2 "Unknown variable `UnboundCheckVar.ink`"
  , errorTest "tests/errors/UnboundFunInSpec.hs"    2 "Illegal type specification for `Goo.three`"
  , errorTest "tests/errors/UnboundFunInSpec1.hs"   2 "Illegal type specification for `Goo.foo`"
  , errorTest "tests/errors/UnboundFunInSpec2.hs"   2 "Illegal type specification for `Goo.foo`"
  , errorTest "tests/errors/UnboundVarInLocSig.hs"  2 "Illegal type specification for `bar`" 
  , errorTest "tests/errors/Fractional.hs"          2 "Illegal type specification for `Crash.f`"
  , errorTest "tests/errors/T773.hs"                2 "Illegal type specification for `LiquidR.incr`"
  , errorTest "tests/errors/T774.hs"                2 "Illegal type specification for `LiquidR.incr`"
  , errorTest "tests/errors/T1498.hs"               2 "Standalone class method refinement"
  , errorTest "tests/errors/T1498A.hs"              2 "Error: Bad Data Specification"
  , errorTest "tests/errors/Inconsistent0.hs"       2 "Specified type does not refine Haskell type for `Ast.id1`" 
  , errorTest "tests/errors/Inconsistent1.hs"       2 "Specified type does not refine Haskell type for `Boo.incr` (Checked)"
  , errorTest "tests/errors/Inconsistent2.hs"       2 "Specified type does not refine Haskell type for `Mismatch.foo` (Checked)"
  , errorTest "tests/errors/BadAliasApp.hs"         2 "Malformed application of type alias `ListN`"
  , errorTest "tests/errors/BadPragma0.hs"          2 "Illegal pragma"
  , errorTest "tests/errors/BadPragma1.hs"          2 "Illegal pragma"
  , errorTest "tests/errors/BadPragma2.hs"          2 "Illegal pragma"
  , errorTest "tests/errors/BadSyn1.hs"             2 "Malformed application of type alias `Fooz`"
  , errorTest "tests/errors/BadSyn2.hs"             2 "Malformed application of type alias `Zoo.Foo`"
  , errorTest "tests/errors/BadSyn3.hs"             2 "Malformed application of type alias `Zoo.Foo`"
  , errorTest "tests/errors/BadSyn4.hs"             2 "Malformed application of type alias `Foo.Point`"
  , errorTest "tests/errors/BadAnnotation.hs"       2 "Malformed annotation"
  , errorTest "tests/errors/BadAnnotation1.hs"      2 "Malformed annotation"
  , errorTest "tests/errors/CyclicExprAlias0.hs"    2 "Cyclic type alias definition"
  , errorTest "tests/errors/CyclicExprAlias1.hs"    2 "Cyclic type alias definition" 
  , errorTest "tests/errors/CyclicExprAlias2.hs"    2 "Cyclic type alias definition"
  , errorTest "tests/errors/CyclicExprAlias3.hs"    2 "Cyclic type alias definition"
  , errorTest "tests/errors/DupAlias.hs"            2 "Multiple definitions of Type Alias `BoundedNat`"
  , errorTest "tests/errors/DupAlias.hs"            2 "Multiple definitions of Pred Alias `Foo`"
  , errorTest "tests/errors/BadDataConType.hs"      2 "Illegal type specification for `Boo.fldY`" 
  , errorTest "tests/errors/BadDataConType1.hs"     2 "Error: Specified type does not refine Haskell type for `Boo.C`" 
                                                       -- "Illegal type specification for `Boo.fldY`" 

  , errorTest "tests/errors/BadDataConType2.hs"     2 "different numbers of fields for `Boo.C`" 
  , errorTest "tests/errors/LiftMeasureCase.hs"     2 "Cannot create measure 'Measures.foo': Does not have a case-of at the top-level"
  , errorTest "tests/errors/HigherOrderBinder.hs"   2 "Illegal type specification for `Main.foo`"
  , errorTest "tests/errors/HoleCrash1.hs"          2 "Illegal type specification for `ListDemo.t`"
  , errorTest "tests/errors/HoleCrash2.hs"          2 "Malformed application of type alias `Geq`"
  , errorTest "tests/errors/HoleCrash3.hs"          2 "Specified type does not refine Haskell type for `ListDemo.countUp`"
  , errorTest "tests/errors/BadPredApp.hs"          2 "Malformed predicate application"
  , errorTest "tests/errors/LocalHole.hs"           2 "Illegal type specification for `go`"
  , errorTest "tests/errors/UnboundAbsRef.hs"       2 "Cannot apply unbound abstract refinement `p`"
  -- , errorTest "tests/errors/BadQualifier.hs"        2 "Illegal qualifier specification for `Foo`"
  , errorTest "tests/errors/ParseClass.hs"          2 "Cannot parse specification"
  , errorTest "tests/errors/ParseBind.hs"           2 "Cannot parse specification"
  , errorTest "tests/errors/MultiInstMeasures.hs"   2 "Multiple instance measures `sizeOf` for type `GHC.Ptr.Ptr`"
  , errorTest "tests/errors/BadDataDeclTyVars.hs"   2 "Mismatch in number of type variables for `L`"
  , errorTest "tests/errors/BadDataCon2.hs"         2 "GHC and Liquid specifications have different numbers of fields for `Boo.Cuthb`"
  , errorTest "tests/errors/BadSig0.hs"             2 "Error: Illegal type specification for `Zoo.foo`"
  , errorTest "tests/errors/BadSig1.hs"             2 "Error: Illegal type specification for `Ev.EZ`"
  , errorTest "tests/errors/BadData1.hs"            2 "`Main.EntityField` is not the type constructed by"
  , errorTest "tests/errors/BadData2.hs"            2 "`Boo.Hog` is not the type constructed by `Cuthb`"
  , errorTest "tests/errors/T1140.hs"               2 "Specified type does not refine Haskell type for `Blank.foo`"
  , errorTest "tests/errors/InlineSubExp0.hs"       1 "== f B C"
  , errorTest "tests/errors/InlineSubExp1.hs"       1 "== f B (g A)"
  , errorTest "tests/errors/EmptySig.hs"            2 "Error: Cannot parse specification"
  , errorTest "tests/errors/MissingReflect.hs"      2 "Error: Illegal type specification for `Main.empty_foo`" 
  , errorTest "tests/errors/MissingSizeFun.hs"      2 "Error: Unknown variable `llen2`" 
  , errorTest "tests/errors/MissingAssume.hs"       2 "Error: Unknown variable `goober`" 
  , errorTest "tests/errors/HintMismatch.hs"        2 "HINT: Use the hole"
  , errorTest "tests/errors/ElabLocation.hs"        2 "ElabLocation.hs:11:14-11:15: Error"
  , errorTest "tests/errors/ErrLocation.hs"         1 "ErrLocation.hs:7:13-19: Error"
  , errorTest "tests/errors/ErrLocation2.hs"        1 "ErrLocation2.hs:9:20: Error"
  -- , errorTest "tests/errors/UnknownTyConHole.hs"    2 "HINT: Use the hole" 
  -- TODO-REBARE ?, errorTest "tests/errors/MissingField1.hs"        2 "Error: Unknown field `goober`" 
  -- TODO-REBARE ?, errorTest "tests/errors/MissingField2.hs"        2 "Error: Unknown field `fxx`" 
  ]

macroTests :: IO TestTree
macroTests = group "Macro"
   [ testGroup "unit-pos"       <$> dirTests "tests/pos"                            posIgnored        ExitSuccess
   , testGroup "unit-neg"       <$> dirTests "tests/neg"                            negIgnored        (ExitFailure 1)
   ] 

microTests :: IO TestTree
microTests = group "Micro"
  [ mkMicro "parser-pos"     "tests/parser/pos"      ExitSuccess
  , mkMicro "basic-pos"      "tests/basic/pos"       ExitSuccess
  , mkMicro "basic-neg"      "tests/basic/neg"       (ExitFailure 1)
  , mkMicro "measure-pos"    "tests/measure/pos"     ExitSuccess          -- measPosOrder
  , mkMicro "measure-neg"    "tests/measure/neg"     (ExitFailure 1)
  , mkMicro "datacon-pos"    "tests/datacon/pos"     ExitSuccess          
  , mkMicro "datacon-neg"    "tests/datacon/neg"     (ExitFailure 1)
  , mkMicro "names-pos"      "tests/names/pos"       ExitSuccess
  , mkMicro "names-neg"      "tests/names/neg"       (ExitFailure 1)
  , mkMicro "reflect-pos"    "tests/reflect/pos"     ExitSuccess
  , mkMicro "reflect-neg"    "tests/reflect/neg"     (ExitFailure 1) 
  , mkMicro "absref-pos"     "tests/absref/pos"      ExitSuccess
  , mkMicro "absref-neg"     "tests/absref/neg"      (ExitFailure 1)
  -- , mkMicro "import-lib"     "tests/import/lib"      ExitSuccess       -- NOT disabled; but via CHECK-IMPORTS
  , mkMicro "import-cli"     "tests/import/client"   ExitSuccess
  , mkMicro "class-pos"      "tests/classes/pos"     ExitSuccess
  , mkMicro "class-neg"      "tests/classes/neg"     (ExitFailure 1)        
  , mkMicro "ple-pos"        "tests/ple/pos"         ExitSuccess
  , mkMicro "ple-neg"        "tests/ple/neg"         (ExitFailure 1)
  , mkMicro "rankN-pos"      "tests/RankNTypes/pos"         ExitSuccess
  , mkMicro "terminate-pos"  "tests/terminate/pos"   ExitSuccess
  , mkMicro "terminate-neg"  "tests/terminate/neg"   (ExitFailure 1)
  , mkMicro "pattern-pos"    "tests/pattern/pos"     ExitSuccess
  , mkMicro "class-laws-pos" "tests/class-laws/pos"  ExitSuccess
  , mkMicro "class-laws-crash" "tests/class-laws/crash" (ExitFailure 2)
  , mkMicro "class-laws-neg"   "tests/class-laws/neg"   (ExitFailure 1)
  , mkMicro "implicit-pos"   "tests/implicit/pos"    ExitSuccess
  , mkMicro "implicit-neg"   "tests/implicit/neg"   (ExitFailure 1)
  -- RJ: disabling because broken by adt PR #1068
  -- , testGroup "gradual/pos"    <$> dirTests "tests/gradual/pos"                    []                ExitSuccess
  -- , testGroup "gradual/neg"    <$> dirTests "tests/gradual/neg"                    []                (ExitFailure 1)
  ]
  where 
    mkMicro name dir res    = testGroup name <$> dirTests  dir [] res 


posIgnored    = [ "mapreduce.hs" ]
gPosIgnored   = ["Intro.hs"]
gNegIgnored   = ["Interpretations.hs", "Gradual.hs"]

benchTests :: IO TestTree
benchTests = group "Benchmarks"
  [ testGroup "esop"        <$> dirTests  "benchmarks/esop2013-submission"        esopIgnored               ExitSuccess
  , testGroup "vect-algs"   <$> odirTests  "benchmarks/vector-algorithms-0.5.4.2" []            vectOrder   ExitSuccess
  , testGroup "bytestring"  <$> odirTests  "benchmarks/bytestring-0.9.2.1"        bsIgnored     bsOrder     ExitSuccess
  , testGroup "text"        <$> odirTests  "benchmarks/text-0.11.2.3"             textIgnored   textOrder   ExitSuccess
  , testGroup "icfp_pos"    <$> odirTests  "benchmarks/icfp15/pos"                icfpIgnored   icfpOrder   ExitSuccess
  , testGroup "icfp_neg"    <$> odirTests  "benchmarks/icfp15/neg"                icfpIgnored   icfpOrder   (ExitFailure 1)
  ]

-- AUTO-ORDER _impLibOrder :: Maybe FileOrder 
-- AUTO-ORDER _impLibOrder = Just . mkOrder $ [ "T1102_LibZ.hs", "WrapLibCode.hs", "STLib.hs", "T1102_LibY.hs" ]
-- AUTO-ORDER 
-- AUTO-ORDER _dconPosOrder :: Maybe FileOrder 
-- AUTO-ORDER _dconPosOrder = Just . mkOrder $ [ "Data02Lib.hs" ]
-- AUTO-ORDER 
-- AUTO-ORDER _measPosOrder :: Maybe FileOrder 
-- AUTO-ORDER _measPosOrder = Just . mkOrder $ [ "List00Lib.hs" ]

proverOrder :: Maybe FileOrder 
proverOrder = Just . mkOrder $ 
  [ "Proves.hs"
  , "Helper.hs" 
  ]

icfpOrder :: Maybe FileOrder 
icfpOrder = Just . mkOrder $ 
  [ "RIO.hs" 
  , "RIO2.hs"
  , "WhileM.hs" 
  , "DataBase.hs"
  ]

vectOrder :: Maybe FileOrder 
vectOrder = Just . mkOrder $ 
  [ "Data/Vector/Algorithms/Common.hs"
  , "Data/Vector/Algorithms/Search.hs"
  , "Data/Vector/Algorithms/Radix.hs"
  , "Data/Vector/Algorithms/Termination.hs"
  , "Data/Vector/Algorithms/Optimal.hs"
  , "Data/Vector/Algorithms/Insertion.hs"
  , "Data/Vector/Algorithms/Merge.hs"
  , "Data/Vector/Algorithms/Heap.hs"
  , "Data/Vector/Algorithms/Intro.hs"
  , "Data/Vector/Algorithms/AmericanFlag.hs" 
  ]  
 
bsOrder :: Maybe FileOrder 
bsOrder = Just . mkOrder $ 
  [ "Data/ByteString/Internal.hs" 
  , "Data/ByteString/Lazy/Internal.hs" 
  , "Data/ByteString/Fusion.hs" 
  , "Data/ByteString/Fusion.T.hs" 
  , "Data/ByteString/Unsafe.hs" 
  , "Data/ByteString.T.hs"
  , "Data/ByteString.hs"
  , "Data/ByteString/Lazy.hs"
  , "Data/ByteString/LazyZip.hs"
  ]

textOrder :: Maybe FileOrder 
textOrder = Just . mkOrder $ 
  [ "Data/Text/Encoding/Utf16.hs"       -- skip
  , "Data/Text/Unsafe/Base.hs"          -- skip
  , "Data/Text/UnsafeShift.hs"          -- skip
  , "Data/Text/Util.hs"
  , "Data/Text/Fusion/Size.hs"
  , "Data/Text/Fusion/Internal.hs"      -- skip
  , "Data/Text/Fusion/CaseMapping.hs"   -- skip
  , "Data/Text/Fusion/Common.hs"        -- skip
  , "Data/Text/Array.hs"
  , "Data/Text/UnsafeChar.hs"
  , "Data/Text/Internal.hs"
  , "Data/Text/Search.hs"
  , "Data/Text/Axioms.hs"               
  , "Data/Text/Unsafe.hs"
  , "Data/Text/Private.hs"
  , "Data/Text/Fusion/Common.hs"
  , "Data/Text/Fusion.hs"
  , "Data/Text/Foreign.hs"
  , "Data/Text.hs"
  , "Data/Text/Lazy/Internal.hs"
  , "Data/Text/Lazy/Search.hs"
  , "Data/Text/Lazy/Fusion.hs"
  , "Data/Text/Lazy.hs"
  , "Data/Text/Lazy/Builder.hs"
  , "Data/Text/Encoding.hs"
  , "Data/Text/Lazy/Encoding.hs"
  ] 
  
-- errorTest "tests/errors/ShadowFieldInline.hs"   2 "Error: Multiple specifications for `pig`"

proverTests :: IO TestTree
proverTests = group "Prover"
  [ testGroup "foundations"     <$> dirTests  "benchmarks/sf"                []                          ExitSuccess
  , testGroup "prover_ple_lib"  <$> odirTests "benchmarks/popl18/lib"        []             proverOrder  ExitSuccess
  , testGroup "without_ple_pos" <$> odirTests "benchmarks/popl18/nople/pos"  noPleIgnored   proverOrder  ExitSuccess
  , testGroup "without_ple_neg" <$> odirTests "benchmarks/popl18/nople/neg"  noPleIgnored   proverOrder (ExitFailure 1)
  , testGroup "with_ple"        <$> odirTests "benchmarks/popl18/ple/pos"    autoIgnored    proverOrder  ExitSuccess
  ]


selfTests :: IO TestTree
selfTests
  = group "Self" [
      testGroup "liquid"      <$> dirTests "src"  [] ExitSuccess
  ]

--------------------------------------------------------------------------------
-- | For each file in `root` check, that we get the given exit `code.`
--------------------------------------------------------------------------------
dirTests :: FilePath -> [FilePath] -> ExitCode -> IO [TestTree]
--------------------------------------------------------------------------------
dirTests root ignored ecode = odirTests root ignored Nothing ecode 

--------------------------------------------------------------------------------
odirTests :: FilePath -> [FilePath] -> Maybe FileOrder -> ExitCode -> IO [TestTree]
--------------------------------------------------------------------------------
odirTests root ignored fo ecode = do 
  files     <- walkDirectory False root
  -- print (show files)
  let tests  = sortOrder fo [ rel | f <- files
                                  , isTest f
                                  , let rel = makeRelative root f
                                  , rel `notElem` ignored 
                            ]
  -- print (show tests)
  return     $ mkCodeTest ecode root <$> tests

mkCodeTest :: ExitCode -> FilePath -> FilePath -> TestTree
mkCodeTest code dir file = mkTest (EC file code Nothing) dir file

isTest   :: FilePath -> Bool
isTest f =  takeExtension f == ".hs"
         || takeExtension f == ".lhs"

--------------------------------------------------------------------------------
-- | @FileOrder@ is a hack to impose a "build" order on the paths in a given directory
--------------------------------------------------------------------------------
type FileOrder = Map.Map FilePath Int 

getOrder :: FileOrder -> FilePath -> Int 
getOrder m f = Map.findWithDefault (1 + Map.size m) f m 

mkOrder :: [FilePath] -> FileOrder 
mkOrder fs = Map.fromList (zip fs [0..])

defaultFileOrder :: [FilePath] -> [FilePath]
defaultFileOrder = L.reverse . sortOn stringLower 

sortOrder :: Maybe FileOrder -> [FilePath] -> [FilePath]
sortOrder Nothing   fs = defaultFileOrder fs 
sortOrder (Just fo) fs = sortOn (getOrder fo) ordFs ++ defaultFileOrder otherFs 
  where 
    (ordFs, otherFs)   = L.partition (`Map.member` fo) fs 

sortOn :: (Ord b) => (a -> b) -> [a] -> [a]
sortOn f = L.sortBy (compare `on` f)

stringLower :: FilePath -> FilePath 
stringLower = fmap toLower

--------------------------------------------------------------------------------
-- | Check that we get the given `err` text and `ExitFailure status` for the given `path`.
--------------------------------------------------------------------------------
errorTest :: FilePath -> Int -> T.Text -> IO TestTree
--------------------------------------------------------------------------------
errorTest path status err = return (mkTest ec dir file)
  where
    ec                    = EC file (ExitFailure status) (Just err)
    (dir, file)           = splitFileName path

--------------------------------------------------------------------------------
data ExitCheck = EC { ecTest :: FilePath, ecCode :: ExitCode, ecLog :: Maybe T.Text }
                 deriving (Show)

ecAssert :: ExitCheck -> ExitCode -> T.Text -> Assertion
ecAssert ec (ExitFailure 137) _   =
  printf "WARNING: possible OOM while testing %s: IGNORING" (ecTest ec)

ecAssert (EC _ code Nothing)  c _   =
  assertEqual "Wrong exit code" code c

ecAssert (EC _ code (Just t)) c log = do
  assertEqual "Wrong exit code" code c
  assertBool ("Did not match message: " ++ T.unpack t) (T.isInfixOf t log)

--------------------------------------------------------------------------------
mkTest :: ExitCheck -> FilePath -> FilePath -> TestTree
--------------------------------------------------------------------------------
mkTest ec dir file
  = askOption $ \(smt :: SmtSolver) -> askOption $ \(opts :: LiquidOpts) -> testCase file $
      if test `elem` knownToFail smt
      then do
        printf "%s is known to fail with %s: SKIPPING" test (show smt)
        assertEqual "" True True
      else do
        createDirectoryIfMissing True $ takeDirectory log
        bin <- binPath "liquid"
        hSetBuffering stdout LineBuffering -- or even NoBuffering
        withFile log WriteMode $ \h -> do
          let cmd     = testCmd bin dir file smt $ mappend (extraOptions dir test) opts
          -- let cmd     = testCmd bin dir file smt $ mappend (extraOptions dir test) $ mappend "-v" opts
          (_,_,_,ph) <- createProcess $ (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
          c          <- waitForProcess ph
          ecAssert ec c =<< T.readFile log
          -- renameFile log $ log <.> (if code == c then "pass" else "fail")
          -- if c == ExitFailure 137
            -- then printf "WARNING: possible OOM while testing %s: IGNORING" test
            -- else assertEqual "Wrong exit code" code c
  where
    test = dir </> file
    log = "tests/logs/cur" </> test <.> "log"

binPath :: FilePath -> IO FilePath
binPath pkgName = (</> pkgName) <$> getBinDir

knownToFail :: SmtSolver -> [FilePath]
knownToFail CVC4 = [ "tests/pos/linspace.hs"
                   , "tests/pos/RealProps.hs"
                   , "tests/pos/RealProps1.hs"
                   , "tests/pos/initarray.hs"
                   , "tests/pos/maps.hs"
                   , "tests/pos/maps1.hs"
                   , "tests/neg/maps.hs"
                   , "tests/pos/Product.hs"
                   , "tests/pos/Gradual.hs"
                   , "tests/equationalproofs/pos/MapAppend.hs"
                   ]

knownToFail Z3   = [ "tests/pos/linspace.hs"
                   , "tests/equationalproofs/pos/MapAppend.hs"
                   ]

--------------------------------------------------------------------------------
extraOptions :: FilePath -> FilePath -> LiquidOpts
--------------------------------------------------------------------------------
extraOptions dir test = mappend (dirOpts dir) (testOpts test)
  where
    dirOpts = flip (Map.findWithDefault mempty) $ Map.fromList
      [ ( "benchmarks/bytestring-0.9.2.1"
        , "-iinclude --c-files=cbits/fpstring.c"
        )
      , ( "benchmarks/text-0.11.2.3"
        , "--no-check-imports -i../bytestring-0.9.2.1 -i../bytestring-0.9.2.1/include --c-files=../bytestring-0.9.2.1/cbits/fpstring.c -i../../include --c-files=cbits/cbits.c"
        )
      , ( "benchmarks/vector-0.10.0.1"
        , "-i."
        )
      , ( "tests/import/client"
        , "-i../lib"
        )
      , ( "benchmarks/popl18/nople/pos"
        , "-i../../lib"
        )
      , ( "benchmarks/popl18/nople/neg"
        , "-i../../lib"
        )
      , ( "benchmarks/popl18/ple/pos"
        , "-i../../lib"
        )
      ]
    testOpts = flip (Map.findWithDefault mempty) $ Map.fromList
      [ ( "tests/pos/Class2.hs"
        , "-i../neg"
        )
      , ( "tests/pos/FFI.hs"
        , "-i../ffi-include --c-files=../ffi-include/foo.c"
        )
      ]

---------------------------------------------------------------------------
testCmd :: FilePath -> FilePath -> FilePath -> SmtSolver -> LiquidOpts -> String
---------------------------------------------------------------------------
testCmd bin dir file smt (LO opts)
  = printf "cd %s && %s -i . --smtsolver %s %s %s" dir bin (show smt) file opts
  -- = printf "%s -i %s --smtsolver %s %s %s" bin dir (show smt) file opts

noPleIgnored :: [FilePath]
noPleIgnored 
  = "ApplicativeList.hs"         -- TODO-REBARE: TODO BLOWUP but ple version ok
  : autoIgnored

esopIgnored 
  = [ "Base0.hs"
    ]

icfpIgnored :: [FilePath]
icfpIgnored 
  = [ "FindRec.hs"
    , "CopyRec.hs"
    , "TwiceM.hs"                -- TODO: BLOWUP: using 2.7GB RAM
    ]

autoIgnored 
  = "Ackermann.hs" 
  : proverIgnored

proverIgnored  :: [FilePath]
proverIgnored 
  = [ "OverviewListInfix.hs"
    -- , "Proves.hs"
    -- , "Helper.hs"
    , "FunctorReader.hs"      -- NOPROP: TODO: Niki please fix!
    , "MonadReader.hs"        -- NOPROP: ""
    , "ApplicativeReader.hs"  -- NOPROP: ""
    , "FunctorReader.NoExtensionality.hs" -- Name resolution issues
    -- , "Fibonacci.hs"          -- REFLECT-IMPORTS: TODO: Niki please fix!
    ]



hscIgnored :: [FilePath]
hscIgnored 
  = [ "HsColour.hs"
    , "Language/Haskell/HsColour/Classify.hs"      -- eliminate
    , "Language/Haskell/HsColour/Anchors.hs"       -- eliminate
    , "Language/Haskell/HsColour/ACSS.hs"          -- eliminate
    ]

negIgnored :: [FilePath]
negIgnored 
  = [ "Lib.hs"
    , "LibSpec.hs"
    ]

bsIgnored :: [FilePath]
bsIgnored 
  = [ "Data/ByteString.T.hs" ]                    -- TODO-REBARE


textIgnored :: [FilePath]
textIgnored 
  = [ "Setup.lhs"
    -- , "Data/Text/Axioms.hs"
    , "Data/Text/Encoding/Error.hs"
    , "Data/Text/Encoding/Fusion.hs"
    , "Data/Text/Encoding/Fusion/Common.hs"
    , "Data/Text/Encoding/Utf16.hs"
    , "Data/Text/Encoding/Utf32.hs"
    , "Data/Text/Encoding/Utf8.hs"
    , "Data/Text/Fusion/CaseMapping.hs"
    , "Data/Text/Fusion/Internal.hs"
    , "Data/Text/IO.hs"
    , "Data/Text/IO/Internal.hs"
    , "Data/Text/Lazy/Builder/Functions.hs"
    , "Data/Text/Lazy/Builder/Int.hs"
    , "Data/Text/Lazy/Builder/Int/Digits.hs"
    , "Data/Text/Lazy/Builder/Internal.hs"
    , "Data/Text/Lazy/Builder/RealFloat.hs"
    , "Data/Text/Lazy/Builder/RealFloat/Functions.hs"
    , "Data/Text/Lazy/Encoding/Fusion.hs"
    , "Data/Text/Lazy/IO.hs"
    , "Data/Text/Lazy/Read.hs"
    , "Data/Text/Read.hs"
    , "Data/Text/Unsafe/Base.hs"
    , "Data/Text/UnsafeShift.hs"
    -- , "Data/Text/Util.hs"
    , "Data/Text/Fusion-debug.hs"
    -- , "Data/Text/Encoding.hs"
    ]

demosIgnored :: [FilePath]
demosIgnored = [ "Composition.hs"
               , "Eval.hs"
               , "Inductive.hs"
               , "Loop.hs"
               , "TalkingAboutSets.hs"
               , "refinements101reax.hs"
               ]

----------------------------------------------------------------------------------------
-- Generic Helpers
----------------------------------------------------------------------------------------
group :: (Monad m) => TestName -> [m TestTree] -> m TestTree
group n xs = testGroup n <$> sequence xs

gitTimestamp :: IO String
gitTimestamp = do
   res <- gitProcess ["show", "--format=\"%ci\"", "--quiet"]
   return $ filter notNoise res

gitEpochTimestamp :: IO String
gitEpochTimestamp = do
   res <- gitProcess ["show", "--format=\"%ct\"", "--quiet"]
   return $ filter notNoise res

gitHash :: IO String
gitHash = do
   res <- gitProcess ["show", "--format=\"%H\"", "--quiet"]
   return $ filter notNoise res

gitRef :: IO String
gitRef = do
   res <- gitProcess ["show", "--format=\"%d\"", "--quiet"]
   return $ filter notNoise res

-- | Calls `git` for info; returns `"plain"` if we are not in a git directory.
gitProcess :: [String] -> IO String
gitProcess args = (readProcess "git" args []) `catchIOError` const (return "plain")

notNoise :: Char -> Bool
notNoise a = a /= '\"' && a /= '\n' && a /= '\r'

headerDelim :: String
headerDelim = replicate 80 '-'

----------------------------------------------------------------------------------------
walkDirectory :: Bool -> FilePath -> IO [FilePath]
----------------------------------------------------------------------------------------
walkDirectory del root = do 
  when del (nukeIfThere (root </> ".liquid"))
  (ds,fs) <- partitionM doesDirectoryExist . candidates =<< (getDirectoryContents root `catchIOError` const (return []))
  (fs ++) <$> concatMapM (walkDirectory del) ds
  where
    candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]

nukeIfThere :: FilePath -> IO () 
nukeIfThere dir = do 
  ex <- doesDirectoryExist dir 
  if ex then removeDirectoryRecursive dir else return () 

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM f = go [] []
  where
    go ls rs []     = return (ls,rs)
    go ls rs (x:xs) = do b <- f x
                         if b then go (x:ls) rs xs
                              else go ls (x:rs) xs

-- isDirectory :: FilePath -> IO Bool
-- isDirectory = fmap Posix.isDirectory . Posix.getFileStatus

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM _ []     = pure []
concatMapM f (x:xs) = (++) <$> f x <*> concatMapM f xs

-- | Combine two @TestReporter@s into one.
--
-- Runs the reporters in sequence, so it's best to start with the one
-- that will produce incremental output, e.g. 'consoleTestReporter'.
combineReporters :: Ingredient -> Ingredient -> Ingredient
combineReporters (TestReporter opts1 run1) (TestReporter opts2 run2)
  = TestReporter (opts1 ++ opts2) $ \opts tree -> do
      f1 <- run1 opts tree
      f2 <- run2 opts tree
      return $ \smap -> f1 smap >> f2 smap
combineReporters _ _ = error "combineReporters needs TestReporters"

type Summary = [(String, Double, Bool)]

-- this is largely based on ocharles' test runner at
-- https://github.com/ocharles/tasty-ant-xml/blob/master/Test/Tasty/Runners/AntXML.hs#L65
loggingTestReporter :: Ingredient
loggingTestReporter = TestReporter [] $ \opts tree -> Just $ \smap -> do
  let
    runTest _ testName _ = Traversal $ Functor.Compose $ do
        i <- State.get

        summary <- lift $ STM.atomically $ do
          status <- STM.readTVar $
            fromMaybe (error "Attempted to lookup test by index outside bounds") $
              IntMap.lookup i smap

          let mkSuccess time = [(testName, time, True)]
              mkFailure time = [(testName, time, False)]

          case status of
            -- If the test is done, generate a summary for it
            Done result
              | resultSuccessful result
                  -> pure (mkSuccess (resultTime result))
              | otherwise
                  -> pure (mkFailure (resultTime result))
            -- Otherwise the test has either not been started or is currently
            -- executing
            _ -> STM.retry

        Const summary <$ State.modify (+ 1)

    runGroup group children = Traversal $ Functor.Compose $ do
      Const soFar <- Functor.getCompose $ getTraversal children
      pure $ Const $ map (\(n,t,s) -> (group</>n,t,s)) soFar

    computeFailures :: StatusMap -> IO Int
    computeFailures = fmap getSum . getApp . foldMap (\var -> Ap $
      (\r -> Sum $ if resultSuccessful r then 0 else 1) <$> getResultFromTVar var)

    getResultFromTVar :: STM.TVar Status -> IO Result
    getResultFromTVar var =
      STM.atomically $ do
        status <- STM.readTVar var
        case status of
          Done r -> return r
          _ -> STM.retry

  (Const summary, _tests) <-
     flip State.runStateT 0 $ Functor.getCompose $ getTraversal $
      foldTestTree
        trivialFold { foldSingle = runTest, foldGroup = runGroup }
        opts
        tree

  return $ \_elapsedTime -> do
    -- get some semblance of a hostname
    host <- takeWhile (/='.') . takeWhile (not . isSpace) <$> readProcess "hostname" [] []
    -- don't use the `time` package, major api differences between ghc 708 and 710
    time <- head . lines <$> readProcess "date" ["+%Y-%m-%dT%H-%M-%S"] []
    -- build header
    ref       <- gitRef
    timestamp <- gitTimestamp
    epochTime <- gitEpochTimestamp
    hash      <- gitHash
    let hdr = unlines [ref ++ " : " ++ hash,
                       "Timestamp: " ++ timestamp,
                       "Epoch Timestamp: " ++ epochTime,
                       headerDelim,
                       "test, time(s), result"]

    let dir = "tests" </> "logs" </> host ++ "-" ++ time
    let smry = "tests" </> "logs" </> "cur" </> "summary.csv"
    writeFile smry $ unlines
                   $ hdr
                   : map (\(n, t, r) -> printf "%s, %0.4f, %s" n t (show r)) summary
    system $ "cp -r tests/logs/cur " ++ dir
    (==0) <$> computeFailures smap
