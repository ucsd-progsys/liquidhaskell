{-# LANGUAGE RecordWildCards #-}

module Test.Summary where

import qualified Data.Text as T
import Test.Types
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Map (Map)
import qualified Data.Map as M
import Data.List (sortOn)

-- | Create a "flavored" ModuleInfoSummary, associating with each module the
-- errors/warnings from stderr (if present), and marking as Safe or Unsafe.
summarizeResults :: Map (Maybe ModuleName) [CompilerMessage] -> TestGroupData -> [ModuleInfo] -> ModuleInfoSummary FlavorSummary
summarizeResults errs tgd modinfos =
  let vanillaResults =
        foldr (\mi' summary ->
                 let mi = mi' { miMessages = M.findWithDefault mempty (Just . chModule . miHeader $ mi') errs }
                 in
                   if null $ filter (\m -> cmMood m == MError) (miMessages mi) then
                     summary { misRan = mi : misRan summary
                             , misSafe = mi : misSafe summary }
                   else
                     summary { misRan = mi :  misRan summary
                             , misUnsafe = mi : misUnsafe summary })
              (ModuleInfoSummary [] [] [] tgd ())
              modinfos
      flavorResults = flavorChecker (\ModuleInfo {..} -> chModule miHeader /= T.pack "Main") errs (tgdFlavor tgd) vanillaResults
  in
    vanillaResults { misSummary = flavorResults }

-- | Create a `FlavorSummary` from the `TestFlavor` that was meant to be run.
-- See `TestFlavor` in `Types.hs` for details on the different flavors.
flavorChecker :: (ModuleInfo -> Bool) -> Map (Maybe ModuleName) [CompilerMessage] -> TestFlavor -> ModuleInfoSummary a -> FlavorSummary
flavorChecker filterPredicate _errs flavor (ModuleInfoSummary {..}) =
  let (diff, alsoErrorMismatch) = case flavor of
        TFSafe -> (misUnsafe, Nothing)
        TFBench -> (misUnsafe, Nothing)
        TFUnsafe -> (misSafe, Nothing)
        TFError errs -> (misSafe, Just $ compareErrors misRan errs)
      filteredDiffList = filter filterPredicate diff
  in
    -- All good if no "failures" and all errors match (if applicable)
    if null filteredDiffList && maybe True null alsoErrorMismatch
    then FSAllGood (length misRan)
    else FSUnexpected (length misRan) (sortOn (chIndex . miHeader) filteredDiffList) alsoErrorMismatch
  where
    compareErrors :: [ModuleInfo] -> Map (Maybe ModuleName) ErrorMsg -> [(ModuleInfo, ErrorMsg)]
    compareErrors xs errors =
      foldr (\mi acc ->
               let errMsg = M.findWithDefault T.empty (Just . chModule . miHeader $ mi) errors
               in
                 if not $ errMsg `T.isInfixOf` T.concat (reshow <$> miMessages mi)
                 then (mi, errMsg) : acc
                 else acc) [] xs

-- | A wrapper around `PP.pretty` that returns a `PP.Doc` representation of the
-- flavored summary.
prettySummarizeResults :: Map (Maybe ModuleName) [CompilerMessage] -> TestGroupData -> [ModuleInfo] -> PP.Doc
prettySummarizeResults errs tgd modinfos = PP.pretty $ summarizeResults errs tgd modinfos
