
-- | This module contains the types for representing dependency
--   graphs between kvars and constraints.

{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Types.Graphs (
  -- * Graphs
    CVertex (..)
  , CEdge
  , KVGraph

  -- * Components
  , Comps
  , KVComps

  -- * Printing
  , writeGraph
  )
  where

import           GHC.Generics              (Generic)
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ

import           Language.Fixpoint.Misc         -- hiding (group)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Refinements -- Constraints

--------------------------------------------------------------------------------

data CVertex = KVar  KVar    -- ^ real kvar vertex
             | DKVar KVar    -- ^ dummy to ensure each kvar has a successor
             | Cstr  Integer -- ^ constraint-id which creates a dependency
               deriving (Eq, Ord, Show, Generic)

instance PPrint CVertex where
  pprint (KVar k)  = doubleQuotes $ pprint $ kv k
  pprint (Cstr i)  = text "id_" <> pprint i
  pprint (DKVar k) = pprint k   <> text "*"


instance Hashable CVertex

type CEdge    = (CVertex, CVertex)
type KVGraph  = [(CVertex, CVertex, [CVertex])]
type Comps a  = [[a]]
type KVComps  = Comps CVertex

--------------------------------------------------------------------------------
writeGraph :: FilePath -> KVGraph -> IO ()
--------------------------------------------------------------------------------
writeGraph f = writeFile f . render . ppGraph

ppGraph :: KVGraph -> Doc
ppGraph g = ppEdges [ (v, v') | (v,_,vs) <- g, v' <- vs]

ppEdges :: [CEdge] -> Doc
ppEdges             = vcat . wrap ["digraph Deps {"] ["}"]
                           . map ppE
                           . filter (not . isJunkEdge)
  where
    ppE (v, v')     = pprint v <+> "->" <+> pprint v'

isJunkEdge :: CEdge -> Bool
isJunkEdge (DKVar _, _)     = True
isJunkEdge (_, DKVar _)     = True
isJunkEdge (Cstr _, Cstr _) = True
isJunkEdge _                = False
