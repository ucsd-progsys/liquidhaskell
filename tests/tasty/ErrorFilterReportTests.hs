module ErrorFilterReportTests(errorFilterReportTests) where

import Test.Tasty ( TestTree, testGroup )
import Test.Tasty.HUnit ( testCase, assertBool )
import Language.Haskell.Liquid.Types (FilterReportErrorsArgs(..))
import Language.Haskell.Liquid.Types.PrettyPrint (Filter(..), filterReportErrorsWith, reduceFilters)
import Data.Functor.Identity (Identity(..))

defArgs :: Monad m => FilterReportErrorsArgs m Filter String String Bool
defArgs = FilterReportErrorsArgs { msgReporter = const (pure ())
                                 , filterReporter = const (pure ())
                                 , failure =  pure False
                                 , continue = pure True
                                 , pprinter = pure
                                 , filterMapper = const (pure [])
                                 , filters = [] }

defFailingArgs :: Monad m => FilterReportErrorsArgs m Filter String String Bool
defFailingArgs = defArgs { failure = continue defArgs
                         , continue = failure defArgs
                         , filterMapper = Left . pure }

-- basic success for empty last arg
emptySuccess :: Monad m => m Bool
emptySuccess = filterReportErrorsWith defArgs []

-- basic failure for non-empty last arg (prints error)
nonemptyFailure :: Monad m => m Bool
nonemptyFailure = filterReportErrorsWith defFailingArgs ["expected error!"]

-- prop: always success no matter what last arg is
alwaysSuccess :: Monad m => m Bool
alwaysSuccess = filterReportErrorsWith
                defArgs { filterMapper = const (Left []) }
                ["unexpected error!"]

-- prop: always success no matter what last arg is (using filterWithFilters)
nonemptySuccessWithFiltersAnyFilter :: Monad m => m Bool
nonemptySuccessWithFiltersAnyFilter = filterReportErrorsWith
                                      defArgs { filterMapper = reduceFilters id filters
                                              , filters = filters }
                                      ["unexpected error!"]
  where
    filters = [AnyFilter]

nonemptySuccessWithFiltersEmptyString :: Monad m => m Bool
nonemptySuccessWithFiltersEmptyString = filterReportErrorsWith
                                        defArgs { filterMapper = reduceFilters id filters
                                                , filters = filters }
                                        ["unexpected error!"]
  where
    filters = [StringFilter ""]

-- prop: for singleton final arg, only succeed when element contains StringFilter string
nonemptyCatchStringFilter :: Monad m => m Bool
nonemptyCatchStringFilter = filterReportErrorsWith
                            defArgs { filterMapper = reduceFilters id filters
                                    , filters = filters}
                            ["error!"]
  where
    filters = [StringFilter "error"]

-- prop: for singleton final arg, only fail when element does not contain StringFilter string (prints error)
nonemptyFailureOnBadStringFilter :: Monad m => m Bool
nonemptyFailureOnBadStringFilter = filterReportErrorsWith
                                   defFailingArgs { filterMapper = reduceFilters id filters
                                                  , filters = filters}
                                   ["expected error!"]
  where
    filters = [StringFilter "this string does not appear in the error"]

testsInIdentity :: [TestTree]
testsInIdentity = (\(testName, test) -> testCase testName $ assertBool "" (runIdentity test)) <$> namedTests
  where
    namedTests = [ ("emptySuccess", emptySuccess)
                 , ("nonemptyFailure", nonemptyFailure)
                 , ("alwaysSuccess", alwaysSuccess)
                 , ("nonemptySuccessWithFiltersAnyFilter", nonemptySuccessWithFiltersAnyFilter)
                 , ("nonemptySuccessWithFiltersEmptyString", nonemptySuccessWithFiltersEmptyString)
                 , ("nonemptyCatchStringFilter", nonemptyCatchStringFilter)
                 , ("nonemptyFailureOnBadStringFilter", nonemptyFailureOnBadStringFilter)
                 ]

errorFilterReportTests :: [TestTree]
errorFilterReportTests = [testGroup "Error Filter in Identity" testsInIdentity]
