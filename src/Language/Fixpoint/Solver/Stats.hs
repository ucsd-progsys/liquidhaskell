{-# LANGUAGE CPP                #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE OverloadedStrings  #-}
module Language.Fixpoint.Solver.Stats where

import           Control.DeepSeq
import           Data.Data
import           Data.Serialize                (Serialize (..))
import           GHC.Generics
import           Text.PrettyPrint.HughesPJ (text)
import qualified Data.Store              as S
import qualified Language.Fixpoint.Types.PrettyPrint as F
import Data.Aeson

#if !MIN_VERSION_base(4,14,0)
import           Data.Semigroup            (Semigroup (..))
#endif

data Stats = Stats 
  { numCstr      :: !Int -- ^ # Horn Constraints
  , numIter      :: !Int -- ^ # Refine Iterations
  , numBrkt      :: !Int -- ^ # smtBracket    calls (push/pop)
  , numChck      :: !Int -- ^ # smtCheckUnsat calls
  , numVald      :: !Int -- ^ # times SMT said RHS Valid
  } deriving (Data, Show, Generic, Eq)

instance NFData Stats
instance S.Store Stats
instance Serialize Stats

instance F.PTable Stats where
  ptable s = F.DocTable [ (text "# Constraints"                       , F.pprint (numCstr      s))
                        , (text "# Refine Iterations"                 , F.pprint (numIter      s))
                        , (text "# SMT Brackets"                      , F.pprint (numBrkt      s))
                        , (text "# SMT Queries (Valid)"               , F.pprint (numVald      s))
                        , (text "# SMT Queries (Total)"               , F.pprint (numChck      s))
                        ]

instance Semigroup Stats where
  s1 <> s2 = 
    Stats { numCstr      = numCstr s1      + numCstr s2
          , numIter      = numIter s1      + numIter s2
          , numBrkt      = numBrkt s1      + numBrkt s2
          , numChck      = numChck s1      + numChck s2
          , numVald      = numVald s1      + numVald s2
          }

instance ToJSON Stats where
  toJSON = genericToJSON defaultOptions
  toEncoding = genericToEncoding defaultOptions

instance FromJSON Stats

instance Monoid Stats where
  mempty  = Stats 0 0 0 0 0
  mappend = (<>)

-- | Returns the Horn clauses checked.
checked :: Stats -> Int
checked = numCstr

-- | Returns a number which can be used in the 'Safe' constructor of a 'FixResult' to show
-- \"the work done\".
totalWork :: Stats -> Int
totalWork Stats{..} = numCstr + numIter + numBrkt + numChck + numVald
