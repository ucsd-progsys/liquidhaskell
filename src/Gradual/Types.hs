module Gradual.Types where


import qualified Language.Haskell.Liquid.UX.Config as C
import Language.Fixpoint.Types

import qualified Data.HashMap.Strict as M

data GConfig = GConfig {depth :: Int}

makeGConfig :: C.Config -> GConfig
makeGConfig cfg = GConfig (C.gdepth cfg)

type GSub a = M.HashMap KVar (a, Expr)

type GMap a = M.HashMap KVar (a, [Expr])

toGMap :: [(KVar, (a, [Expr]))] -> GMap a
toGMap = M.fromList 

fromGMap :: GMap a -> [(KVar, (a, [Expr]))]
fromGMap = M.toList


fromGSub :: GSub a -> [(KVar, (a, Expr))]
fromGSub = M.toList


removeInfo :: GMap a -> GMap ()
removeInfo = M.map (\(_,x) -> ((),x))