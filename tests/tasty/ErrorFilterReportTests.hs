module ErrorFilterReportTests(errorFilterReportTests) where

import Control.Monad.State (State, execState, modify)
import Test.Tasty ( TestTree, testGroup )
import Test.Tasty.HUnit ( testCase, assertBool )
import Language.Haskell.Liquid.Types.PrettyPrint (FilterReportErrorsArgs(..))
import Language.Haskell.Liquid.Types.PrettyPrint (Filter(..), filterReportErrorsWith, reduceFilters)
import Data.Functor.Identity (Identity(..))

defArgs :: FilterReportErrorsArgs (State Int) Filter String String
defArgs = FilterReportErrorsArgs { errorReporter = \xs -> modify (length xs +)
                                 , filterReporter = \xs -> modify (length xs +)
                                 , matchingFilters = const []
                                 , filters = [] }

-- basic success for empty last arg
emptySuccess :: (Int, State Int ())
emptySuccess = (0, filterReportErrorsWith defArgs [])

-- basic failure for non-empty last arg (prints error)
nonemptyFailure :: (Int, State Int ())
nonemptyFailure = (1, filterReportErrorsWith defArgs ["expected error!"])

-- prop: always success no matter what last arg is (using filterWithFilters)
nonemptySuccessWithFiltersAnyFilter :: (Int, State Int ())
nonemptySuccessWithFiltersAnyFilter =
    (,) 0 $
    filterReportErrorsWith
       defArgs { matchingFilters = reduceFilters id filters
               , filters = filters }
       ["unexpected error!"]
  where
    filters = [AnyFilter]

nonemptySuccessWithFiltersEmptyString :: (Int, State Int ())
nonemptySuccessWithFiltersEmptyString =
    (,) 0 $
    filterReportErrorsWith
      defArgs { matchingFilters = reduceFilters id filters
              , filters = filters }
      ["unexpected error!"]
  where
    filters = [StringFilter ""]

-- prop: for singleton final arg, only succeed when element contains StringFilter string
nonemptyCatchStringFilter :: (Int, State Int ())
nonemptyCatchStringFilter =
   (,) 0 $
   filterReportErrorsWith
     defArgs { matchingFilters = reduceFilters id filters
             , filters = filters}
             ["error!"]
  where
    filters = [StringFilter "error"]

-- prop: for singleton final arg, only fail when element does not contain StringFilter string (prints error)
nonemptyFailureOnBadStringFilter :: (Int, State Int ())
nonemptyFailureOnBadStringFilter =
    (,) 1 $
    filterReportErrorsWith
      defArgs { matchingFilters = reduceFilters id filters
              , filters = filters}
      ["expected error!"]
  where
    filters = [StringFilter "this string does not appear in the error"]

testList :: [TestTree]
testList =
    (\(testName, (expected, test)) ->
      testCase testName $ assertBool "" (expected == execState test 0)
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
