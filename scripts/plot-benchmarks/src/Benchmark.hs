{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module Benchmark where

import Data.Csv
import qualified Data.Map as Map
import Data.Foldable
import Data.Time.LocalTime

data Benchmark =
   Benchmark { benchName :: String,
               benchTimestamp :: LocalTime,
               benchTime :: Double,
               benchPass :: Bool
               }
   deriving (Eq)

instance Ord Benchmark where
   compare lhs rhs = compare (benchTimestamp lhs) (benchTimestamp rhs)

unionAppend :: Map.Map String [Benchmark]
               -> Map.Map String Benchmark
               -> Map.Map String [Benchmark]
unionAppend l r = Map.unionWith (++) l r'
   where
      r' = fmap (\a -> [a]) r

toBenchMap :: (Foldable f)
              => f Benchmark
              -> Map.Map String Benchmark
toBenchMap f = foldl' fn Map.empty f
   where
      fn m b = Map.insert (benchName b) b m

instance FromRecord Benchmark where
   parseRecord r = Benchmark
                   <$> r .! 0
                   <*> pure (error ("Shouldn't be evaluated until after"
                                    ++ " reassignment!"))
                   <*> r .! 1
                   <*> do asStr <- r .! 2
                          return $ read asStr {- Since the test suite
   generates this field by calling show, this read Should Be Safe (TM) -}

csvOutName = "Name"
csvOutDate = "Committer Date"
csvOutTime = "Time (Seconds)"
csvOutPass = "Success"

instance ToNamedRecord (LocalTime, Benchmark) where
   toNamedRecord (_, bm) = namedRecord [csvOutName .= benchName bm,
                                   csvOutDate .= (show $ benchTimestamp bm),
                                   csvOutTime .= (benchTime bm),
                                   csvOutPass .= (show $ benchPass bm)]
