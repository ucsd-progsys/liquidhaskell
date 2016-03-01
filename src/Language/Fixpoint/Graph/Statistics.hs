{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE RecordWildCards       #-}

module Language.Fixpoint.Graph.Statistics ( graphStatistics ) where

import           Prelude hiding (init)
import           Control.Monad             (when)
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.PrettyPrint
import qualified Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Graph.Types
import           Language.Fixpoint.Graph.Deps
import           Language.Fixpoint.Graph.Reducible  (isReducible)
import qualified Data.HashSet                         as S
import qualified Data.HashMap.Strict                  as M
import           Text.PrettyPrint.HughesPJ

-- import qualified Data.List                            as L
-- import qualified Data.Graph                           as G
-- import qualified Data.Tree                            as T
-- import           Data.Function (on)
-- import           Data.Hashable
-- import           Data.List (sortBy)

--------------------------------------------------------------------------------
graphStatistics :: Config -> F.SInfo a -> IO ()
--------------------------------------------------------------------------------
graphStatistics cfg si = when (elimStats cfg) $ do
  writeGraph f  (kvGraph si)
  appendFile f . ppc . ptable $ graphStats cfg si
  where
    f     = queryFile Dot cfg
    ppc d = showpp $ vcat [" ", " ", "/*", pprint d, "*/"]

data Stats = Stats {
    stNumKVCuts   :: !Int   -- ^ number of kvars whose removal makes deps acyclic
  , stNumKVNonLin :: !Int   -- ^ number of kvars that appear >= 2 in some LHS
  , stNumKVTotal  :: !Int   -- ^ number of kvars
  , stIsReducible :: !Bool  -- ^ is dep-graph reducible
  , stSetKVNonLin :: S.HashSet F.KVar -- ^ set of non-linear kvars
  }

instance PTable Stats where
  ptable (Stats {..})  = DocTable [
      ("# KVars [Cut]"    , pprint stNumKVCuts)
    , ("# KVars [NonLin]" , pprint stNumKVNonLin)
    , ("# KVars [All]"    , pprint stNumKVTotal)
    , ("# Reducible"      , pprint stIsReducible)
    , ("KVars NonLin"     , pprint stSetKVNonLin)
    ]

graphStats :: Config -> F.SInfo a -> Stats
graphStats cfg si = Stats {
    stNumKVCuts   = S.size (depCuts d)
  , stNumKVNonLin = S.size  nlks
  , stNumKVTotal  = S.size (depCuts d) + S.size (depNonCuts d)
  , stIsReducible = isReducible si
  , stSetKVNonLin = nlks
  }
  where
    nlks          = nlKVars si
    d             = elimVars cfg si

nlKVars :: (F.TaggedC c a) => F.GInfo c a -> S.HashSet F.KVar
nlKVars fi = S.unions $ nlKVarsC bs <$> cs
  where
    bs     = F.bs fi
    cs     = M.elems (F.cm fi)

nlKVarsC :: (F.TaggedC c a) => F.BindEnv -> c a -> S.HashSet F.KVar
nlKVarsC bs c = S.fromList [ k |  (k, n) <- V.envKVarsN bs c, n >= 2]
