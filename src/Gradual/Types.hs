module Gradual.Types where

import Language.Fixpoint.Types

import qualified Data.HashMap.Strict as M


type GSub   = M.HashMap KVar Expr

type GMap a = M.HashMap KVar (a, [Expr])

toGMap :: [(KVar, (a, [Expr]))] -> GMap a
toGMap = M.fromList 

fromGMap :: GMap a -> [(KVar, (a, [Expr]))]
fromGMap = M.toList