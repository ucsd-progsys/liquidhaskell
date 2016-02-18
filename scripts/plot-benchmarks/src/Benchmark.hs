{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Benchmark where

import Data.Csv
import qualified Data.Map as Map
import Data.Foldable

-- TODO: need some notion of time the benchmark occurred

data Benchmark =
   Benchmark { benchName :: String,
               benchTimestamp :: Int,
               benchTime :: Double,
               benchPass :: Bool
               }
   deriving (Show, Eq)

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
                   <*> pure (-1)
                   <*> r .! 1
                   <*> do asStr <- r .! 2
                          return $ read asStr {- Since the test suite
   generates this field by calling show, this read Should Be Safe (TM) -}
