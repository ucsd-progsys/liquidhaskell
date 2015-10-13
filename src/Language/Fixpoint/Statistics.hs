-- | This module implements functions that print out
--   statistics about the constraints.
module Language.Fixpoint.Statistics (statistics) where

import           Control.Arrow ((&&&))

import           Language.Fixpoint.Misc                (donePhase, Moods(..), applyNonNull)
import           Language.Fixpoint.Config
import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Partition           (partition')
import qualified Language.Fixpoint.Types        as F
import qualified Data.HashMap.Strict            as M
import           Data.List (sort,group)
import           Text.PrettyPrint.HughesPJ

statistics :: Config -> F.FInfo a -> IO (F.Result a)
statistics _ fi = do
  let (_, fis) = partition' Nothing fi
  putStrLn $ render $ pprint $ partitionStats fis
  donePhase Loud "Statistics"
  return mempty

partitionStats :: [F.FInfo a] -> Maybe Stats
partitionStats fis = info
  where
    css            = [M.keys $ F.cm fi | fi <- fis]
    sizes          = fromIntegral . length <$> css
    info           = applyNonNull Nothing (Just . mkStats) sizes

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

data Stats = Stats { cSizes  :: [Float]
                   , cFreq   :: [(Float, Int)]
                   , cTotal  :: Float
                   , cMean   :: Float
                   , cMax    :: Float
                   , cSpeed  :: Float
                   } deriving (Show)

instance PPrint Stats where
  pprint s = vcat [ text "STAT: max/total = " <+> pprint (cMax   s) <+> text "/" <+> pprint (cTotal s)
                  , text "STAT: freqs     = " <+> pprint (cFreq  s)
                  , text "STAT: average   = " <+> pprint (cMean  s)
                  , text "STAT: speed     = " <+> pprint (cSpeed s)
                  ]

mkStats :: [Float] -> Stats
mkStats ns  = Stats {
    cSizes  = ns
  , cFreq   = frequency ns
  , cTotal  = total
  , cMean   = avg
  , cMax    = maxx
  , cSpeed  = total / maxx
  }
  where
    maxx    = maximum ns
    total   = sum  ns
    avg     = mean ns

frequency :: (Ord a) => [a] -> [(a, Int)]
frequency = map (head &&& length) . group . sort

stdDev :: [Float] -> Float
stdDev xs   = sqrt (sum [(x - μ)^2 | x <- xs] / n)
  where
    μ       = mean   xs
    n       = fromIntegral $ length xs

mean :: [Float] -> Float
mean ns  = sum ns / fromIntegral (length ns)
