module ErrorFilterReportTests(errorFilterReportTests) where

import Control.Monad.State (State, execState, modify)
import Test.Tasty ( TestTree, testGroup )
import Test.Tasty.HUnit ( testCase, assertBool )
import Language.Haskell.Liquid.Types.PrettyPrint (FilterReportErrorsArgs(..))
import Language.Haskell.Liquid.Types.PrettyPrint (Filter(..), filterReportErrorsWith, reduceFilters)
import Data.Functor.Identity (Identity(..))

defArgs :: FilterReportErrorsArgs (State Int) Filter String String
defArgs = FilterReportErrorsArgs { errorReporter = const (pure ())
                                 , filterReporter = \xs -> modify (length xs +)
                                 , matchingFilters = const []
                                 , filters = [] }

defFailingArgs :: FilterReportErrorsArgs (State Int) Filter String String
defFailingArgs = defArgs { matchingFilters = const [] }

-- basic success for empty last arg
emptySuccess :: State Int ()
emptySuccess = filterReportErrorsWith defArgs []

-- basic failure for non-empty last arg (prints error)
nonemptyFailure :: State Int ()
nonemptyFailure = filterReportErrorsWith defFailingArgs ["expected error!"]

-- prop: always success no matter what last arg is (using filterWithFilters)
nonemptySuccessWithFiltersAnyFilter :: State Int ()
nonemptySuccessWithFiltersAnyFilter = filterReportErrorsWith
                                      defArgs { matchingFilters = reduceFilters id filters
                                              , filters = filters }
                                      ["unexpected error!"]
  where
    filters = [AnyFilter]

nonemptySuccessWithFiltersEmptyString :: State Int ()
nonemptySuccessWithFiltersEmptyString = filterReportErrorsWith
                                        defArgs { matchingFilters = reduceFilters id filters
                                                , filters = filters }
                                        ["unexpected error!"]
  where
    filters = [StringFilter ""]

-- prop: for singleton final arg, only succeed when element contains StringFilter string
nonemptyCatchStringFilter :: State Int ()
nonemptyCatchStringFilter = filterReportErrorsWith
                            defArgs { matchingFilters = reduceFilters id filters
                                    , filters = filters}
                            ["error!"]
  where
    filters = [StringFilter "error"]

-- prop: for singleton final arg, only fail when element does not contain StringFilter string (prints error)
nonemptyFailureOnBadStringFilter :: State Int ()
nonemptyFailureOnBadStringFilter = filterReportErrorsWith
                                   defFailingArgs { matchingFilters = reduceFilters id filters
                                                  , filters = filters}
                                   ["expected error!"]
  where
    filters = [StringFilter "this string does not appear in the error"]

testList :: [TestTree]
testList =
    (\(testName, test) ->
      testCase testName $ assertBool "" (0 == execState test 0)
    ) <$> namedTests
  where
    namedTests = [ ("emptySuccess", emptySuccess)
                 , ("nonemptyFailure", nonemptyFailure)
                 , ("nonemptySuccessWithFiltersAnyFilter", nonemptySuccessWithFiltersAnyFilter)
                 , ("nonemptySuccessWithFiltersEmptyString", nonemptySuccessWithFiltersEmptyString)
                 , ("nonemptyCatchStringFilter", nonemptyCatchStringFilter)
                 , ("nonemptyFailureOnBadStringFilter", nonemptyFailureOnBadStringFilter)
                 ]

errorFilterReportTests :: [TestTree]
errorFilterReportTests = [testGroup "Error Filter" testList]
