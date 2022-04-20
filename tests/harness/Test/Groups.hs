{-# LANGUAGE OverloadedStrings #-}

module Test.Groups where

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified System.FilePath as FP
import System.Environment (lookupEnv)
import Test.Types


microTestGroups :: [TestGroupData]
microTestGroups =
  [ -- micros
    TestGroupData "unit-pos" ["pos"] TFSafe
  , TestGroupData "unit-neg" ["neg"] TFUnsafe
  , TestGroupData "basic-pos" ["basic/pos"] TFSafe
  , TestGroupData "basic-neg" ["basic/neg"] TFUnsafe
  , TestGroupData "class-pos" ["classes/pos"] TFSafe
  , TestGroupData "class-neg" ["classes/neg"] TFUnsafe
  , TestGroupData "parser-pos" ["parser/pos"] TFSafe
  , TestGroupData "measure-pos" ["measure/pos"] TFSafe
  , TestGroupData "measure-neg" ["measure/neg"] TFUnsafe
  , TestGroupData "datacon-pos" ["datacon/pos"] TFSafe
  , TestGroupData "datacon-neg" ["datacon/neg"] TFUnsafe
  , TestGroupData "names-pos" ["names/pos"] TFSafe
  , TestGroupData "names-neg" ["names/neg"] TFUnsafe
  , TestGroupData "reflect-pos" ["reflect/pos"] TFSafe
  , TestGroupData "reflect-neg" ["reflect/neg"] TFUnsafe
  , TestGroupData "absref-pos" ["absref/pos"] TFSafe
  , TestGroupData "absref-neg" ["absref/neg"] TFUnsafe
  , TestGroupData "import-cli" ["import/client", "import/lib"] TFSafe
  , TestGroupData "ple-pos" ["ple/pos"] TFSafe
  , TestGroupData "ple-neg" ["ple/neg"] TFUnsafe
  , TestGroupData "rankN-pos" ["RankNTypes/pos"] TFSafe
  , TestGroupData "terminate-pos" ["terminate/pos"] TFSafe
  , TestGroupData "terminate-neg" ["terminate/neg"] TFUnsafe
  ]

benchmarkTestGroups :: [TestGroupData]
benchmarkTestGroups =
  [ -- benchmarks
    TestGroupData "benchmark-stitch-lh" ["benchmarks/stitch-lh"] TFBench
    -- XXX(matt.walker): I can't get this to work yet, but it mysteriously
    --                   works in the old test framework...
    -- , TestGroupData "benchmark-text" "benchmarks/text-0.11.2.3" TFBench
  , TestGroupData "benchmark-bytestring" ["benchmarks/bytestring-0.9.2.1"] TFBench
  , TestGroupData "benchmark-vector-algorithms" ["benchmarks/vector-algorithms-0.5.4.2"] TFBench
  , TestGroupData "benchmark-cse230" ["benchmarks/cse230/src/Week10"] TFBench
  , TestGroupData "benchmark-esop2013" ["benchmarks/esop2013-submission"] TFBench
  , TestGroupData "benchmark-icfp15-pos" ["benchmarks/icfp15/pos"] TFBench
  , TestGroupData "benchmark-icfp15-neg" ["benchmarks/icfp15/neg"] TFUnsafe
  ]

proverTestGroups :: [TestGroupData]
proverTestGroups =
  [ -- prover
    TestGroupData "prover-foundations" ["benchmarks/sf"] TFBench
    -- NOTE: This is compiled automatically as a dependency
    --, TestGroupData "prover-ple-lib" "benchmarks/popl18/lib" TFBench
  , TestGroupData "prover-ple-pos" ["benchmarks/popl18/ple/pos"] TFBench
  , TestGroupData "prover-nople-pos" ["benchmarks/popl18/nople/pos"] TFBench
  , TestGroupData "prover-nople-neg" ["benchmarks/popl18/nople/neg"] TFUnsafe
  ]

errorsTestGroups :: [TestGroupData]
errorsTestGroups =
  [ -- error messages
    TestGroupData "errors" ["errors"] (TFError errorMsgs)
  ]


allowStackPaths :: [TestGroupData] -> IO (Map TestGroupName TestGroupData)
allowStackPaths xs = do
  -- This is irrefutable!
  Just pwd <- lookupEnv "PWD"
  pure
    $ M.fromList
    $ fmap (\tgd -> ( tgdName tgd
                    , tgd { tgdDirectories =
                              concatMap (\d -> [T.pack $ pwd FP.</> "tests" FP.</> T.unpack d, d])
                              $ tgdDirectories tgd }))
    $ xs


-- | When you want to add a new test group, create a cabal executable for it in
-- tests.cabal and add it here. See `TestFlavor` for information on the
-- different flavors of test groups. Note that this calls a function that gets
-- the pwd so that we can absolute-ify the paths, which stack outputs (cabal
-- uses relative paths).
allTestGroups :: IO (Map TestGroupName TestGroupData)
allTestGroups = allowStackPaths allTestGroupDataPlain

-- | Update this when you add new "classes" of `TestGroupData`
allTestGroupDataPlain :: [TestGroupData]
allTestGroupDataPlain =
  mconcat [ microTestGroups
          , benchmarkTestGroups
          , proverTestGroups
          , errorsTestGroups
          ]

allTestGroupNames :: [TestGroupName]
allTestGroupNames = tgdName <$> allTestGroupDataPlain

-- * `TFError`-flavored tests are tests which we check the error message to make
--   sure it matches what we expect (using `T.isInfixOf`). Below are some
--   functions for constructing the mappings from `ModuleName`s to expected
--   `ErrorMsg` fragments.
--
--   All error-flavored tests are assumed to live on the filesystem in a flat
--   directory. Do not attempt to use `Modules.That.Look.Like.This` (i.e.
--   hierarchical modules) with these functions.

-- | Constructs an `ErrorMsg` Map from an input `FilePath` and a `String`
-- expected error message fragment.
errorTest :: FilePath -> String -> Map (Maybe ModuleName) ErrorMsg
errorTest fp e = M.singleton (Just . T.pack . FP.takeBaseName $ fp) (T.pack e)

-- | A large map of all the `ErrorMsg` fragments for the `errors` TestGroup.
errorMsgs :: Map (Maybe ModuleName) ErrorMsg
errorMsgs = M.unions
  [ 
    -- errorTest "tests/errors/ExportMeasure0.hs"      2 "Cannot lift `llen` into refinement logic"
    -- errorTest "tests/errors/ExportReflect0.hs"      2 "Cannot lift `identity` into refinement logic"
    -- errorTest "tests/errors/ExportMeasure1.hs"      2 "Cannot lift `psnd` into refinement logic"
    -- , errorTest "tests/errors/ShadowMeasureVar.hs"    2 "Multiple specifications for `shadow`"
    -- , errorTest "tests/errors/AmbiguousReflect.hs"    2 "Ambiguous specification symbol `mappend`"
    -- , errorTest "tests/errors/AmbiguousInline.hs"     2 "Ambiguous specification symbol `min`"
    -- , errorTest "tests/errors/MissingAbsRefArgs.hs"   2 "Illegal type specification for `Fixme.bar`"

    errorTest "tests/errors/ReWrite8.hs"            "Could not generate any rewrites from equality"
  , errorTest "tests/errors/ReWrite7.hs"            "Could not generate any rewrites from equality"
  , errorTest "tests/errors/ReWrite6.hs"            "Unable to use ReWrite6.bad as a rewrite because it does not prove an equality"
  , errorTest "tests/errors/ReWrite5.hs"            "parameter \"xs\" contains an inner refinement"
  , errorTest "tests/errors/ShadowFieldInline.hs"   "Multiple specifications for `pig`"
  , errorTest "tests/errors/ShadowFieldReflect.hs"  "Multiple specifications for `pig`"
  , errorTest "tests/errors/MultiRecSels.hs"        "Duplicated definitions for field `left`" 
  , errorTest "tests/errors/DupFunSigs.hs"          "Multiple specifications for `DupFunSigs.fromWeekDayNum`"
  , errorTest "tests/errors/DupMeasure.hs"          "Multiple specifications for `lenA`"
  , errorTest "tests/errors/ShadowMeasure.hs"       "Multiple specifications for `shadow`"
  , errorTest "tests/errors/DupData.hs"             "Multiple specifications for `OVec`"
  , errorTest "tests/errors/EmptyData.hs"           "one or more fields in the data declaration for `A`"
  , errorTest "tests/errors/BadGADT.hs"             "Specified type does not refine Haskell type for `BadGADT.Nil2`" 
  , errorTest "tests/errors/TerminationExprSort.hs" "Illegal termination specification for `TerminationExprSort.showSep`"
  , errorTest "tests/errors/TerminationExprNum.hs"  "Illegal termination specification for `TerminationExprNum.showSep`"
  , errorTest "tests/errors/TerminationExprUnb.hs"  "Illegal termination specification for `go`"
  , errorTest "tests/errors/UnboundVarInSpec.hs"    "Illegal type specification for `UnboundVarInSpec.foo`"
  , errorTest "tests/errors/UnboundVarInAssume.hs"  "Illegal type specification for `UnboundVarInAssume.incr`"
  -- XXX(matt.walker) disabled because Fixpoint.Types.dummyLoc is impossible to associate with a location
  -- , errorTest "tests/errors/UnboundCheckVar.hs"     "Unknown variable `UnboundCheckVar.ink`"
  , errorTest "tests/errors/UnboundFunInSpec.hs"    "Illegal type specification for `UnboundFunInSpec.three`"
  , errorTest "tests/errors/UnboundFunInSpec1.hs"   "Illegal type specification for `UnboundFunInSpec1.foo`"
  , errorTest "tests/errors/UnboundFunInSpec2.hs"   "Illegal type specification for `UnboundFunInSpec2.foo`"
  , errorTest "tests/errors/UnboundVarInLocSig.hs"  "Illegal type specification for `bar`" 
  , errorTest "tests/errors/UnboundVarInReflect.hs" "Illegal type specification for `UnboundVarInReflect.frog`" 
  , errorTest "tests/errors/Fractional.hs"          "Illegal type specification for `Fractional.f`"
  , errorTest "tests/errors/T773.hs"                "Illegal type specification for `T773.incr`"
  , errorTest "tests/errors/T774.hs"                "Illegal type specification for `T774.incr`"
  , errorTest "tests/errors/T1498.hs"               "Standalone class method refinement"
  , errorTest "tests/errors/T1498A.hs"              "Bad Data Specification"
  , errorTest "tests/errors/Inconsistent0.hs"       "Specified type does not refine Haskell type for `Inconsistent0.id1`" 
  , errorTest "tests/errors/Inconsistent1.hs"       "Specified type does not refine Haskell type for `Inconsistent1.incr` (Checked)"
  , errorTest "tests/errors/Inconsistent2.hs"       "Specified type does not refine Haskell type for `Inconsistent2.foo` (Checked)"
  , errorTest "tests/errors/BadAliasApp.hs"         "Malformed application of type alias `ListN`"
  , errorTest "tests/errors/BadPragma0.hs"          "Illegal pragma"
  , errorTest "tests/errors/BadPragma1.hs"          "Illegal pragma"
  , errorTest "tests/errors/BadPragma2.hs"          "Illegal pragma"
  , errorTest "tests/errors/BadSyn1.hs"             "Malformed application of type alias `Fooz`"
  , errorTest "tests/errors/BadSyn2.hs"             "Malformed application of type alias `BadSyn2.Foo`"
  , errorTest "tests/errors/BadSyn3.hs"             "Malformed application of type alias `BadSyn3.Foo`"
  , errorTest "tests/errors/BadSyn4.hs"             "Malformed application of type alias `BadSyn4.Point`"
  , errorTest "tests/errors/BadAnnotation.hs"       "Malformed annotation"
  , errorTest "tests/errors/BadAnnotation1.hs"      "Malformed annotation"
  , errorTest "tests/errors/CyclicExprAlias0.hs"    "Cyclic type alias definition"
  , errorTest "tests/errors/CyclicExprAlias1.hs"    "Cyclic type alias definition" 
  , errorTest "tests/errors/CyclicExprAlias2.hs"    "Cyclic type alias definition"
  , errorTest "tests/errors/CyclicExprAlias3.hs"    "Cyclic type alias definition"
  , errorTest "tests/errors/DupAlias.hs"            "Multiple definitions of Type Alias `BoundedNat`"
  , errorTest "tests/errors/DupAlias.hs"            "Multiple definitions of Pred Alias `Foo`"
  , errorTest "tests/errors/BadData0.hs"            "Unknown type constructor `Zoog`" 
  , errorTest "tests/errors/BadDataConType.hs"      "Illegal type specification for `BadDataConType.fldY`" 
  , errorTest "tests/errors/BadDataConType1.hs"     "Specified type does not refine Haskell type for `BadDataConType1.C`" 
                                                       -- "Illegal type specification for `Boo.fldY`" 

  , errorTest "tests/errors/BadDataConType2.hs"     "different numbers of fields for `BadDataConType2.C`" 
  , errorTest "tests/errors/LiftMeasureCase.hs"     "Cannot create measure 'LiftMeasureCase.foo': Does not have a case-of at the top-level"
  , errorTest "tests/errors/HigherOrderBinder.hs"   "Illegal type specification for `HigherOrderBinder.foo`"
  , errorTest "tests/errors/HoleCrash1.hs"          "Illegal type specification for `HoleCrash1.t`"
  , errorTest "tests/errors/HoleCrash2.hs"          "Malformed application of type alias `Geq`"
  , errorTest "tests/errors/HoleCrash3.hs"          "Specified type does not refine Haskell type for `HoleCrash3.countUp`"
  , errorTest "tests/errors/BadPredApp.hs"          "Malformed predicate application"
  , errorTest "tests/errors/LocalHole.hs"           "Illegal type specification for `go`"
  , errorTest "tests/errors/UnboundAbsRef.hs"       "Cannot apply unbound abstract refinement `p`"
  -- , errorTest "tests/errors/BadQualifier.hs"        2 "Illegal qualifier specification for `Foo`"
  , errorTest "tests/errors/ParseClass.hs"          "Cannot parse specification"
  , errorTest "tests/errors/ParseBind.hs"           "Cannot parse specification"
  , errorTest "tests/errors/MultiInstMeasures.hs"   "Multiple instance measures `sizeOf` for type `GHC.Ptr.Ptr`"
  , errorTest "tests/errors/BadDataDeclTyVars.hs"   "Mismatch in number of type variables for `L`"
  , errorTest "tests/errors/BadDataCon2.hs"         "GHC and Liquid specifications have different numbers of fields for `BadDataCon2.Cuthb`"
  , errorTest "tests/errors/BadSig0.hs"             "Illegal type specification for `BadSig0.foo`"
  , errorTest "tests/errors/BadSig1.hs"             "Illegal type specification for `BadSig1.EZ`"
  , errorTest "tests/errors/BadData1.hs"            "Data constructors in refinement do not match original datatype for `EntityField`"
  , errorTest "tests/errors/BadData2.hs"            "Data constructors in refinement do not match original datatype for `Hog`"
  , errorTest "tests/errors/T1140.hs"               "Specified type does not refine Haskell type for `T1140.foo`"
  , errorTest "tests/errors/InlineSubExp0.hs"       "== f B C"
  , errorTest "tests/errors/InlineSubExp1.hs"       "= f B (g A)"
  , errorTest "tests/errors/EmptySig.hs"            "Cannot parse specification"
  , errorTest "tests/errors/MissingReflect.hs"      "Illegal type specification for `MissingReflect.empty_foo`" 
  , errorTest "tests/errors/MissingSizeFun.hs"      "Unknown variable `llen2`" 
  , errorTest "tests/errors/MissingAssume.hs"       "Unknown variable `goober`" 
  , errorTest "tests/errors/HintMismatch.hs"        "HINT: Use the hole"
  -- XXX(matt.walker): disabled because it prints the error to stdout (!!)
  -- , errorTest "tests/errors/ElabLocation.hs"        "ElabLocation.hs:13:14-13:15: Error"
  , errorTest "tests/errors/ErrLocation.hs"         "ErrLocation.hs:9:13"
  , errorTest "tests/errors/ErrLocation2.hs"        "ErrLocation2.hs:11:20:error"
  , errorTest "tests/errors/Frog.hs"                "Unbound symbol GHC.Err.undefined"
  , errorTest "tests/errors/T1708.hs"               "Unbound symbol T1708.bool1"
  , errorTest "tests/errors/SplitSubtype.hs"        "| VV > 5}"
  -- , errorTest "tests/errors/UnknownTyConHole.hs"    2 "HINT: Use the hole" 
  -- TODO-REBARE ?, errorTest "tests/errors/MissingField1.hs"        2 "Error: Unknown field `goober`" 
  -- TODO-REBARE ?, errorTest "tests/errors/MissingField2.hs"        2 "Error: Unknown field `fxx`" 
  , errorTest "tests/errors/PositivityCheck.hs"     "Negative occurence of PositivityCheck.Bad1"
  , errorTest "tests/errors/Positivity1.hs"         "Negative occurence of Positivity1.Rec"
  , errorTest "tests/errors/Positivity2.hs"         "Negative occurence of Positivity2.Evil in Positivity2.Very"
  ]
