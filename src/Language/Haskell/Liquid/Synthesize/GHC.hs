{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
module Language.Haskell.Liquid.Synthesize.GHC where

import Var 
import TyCoRep
import CoreSyn

import IdInfo
import OccName
import Unique 
import Name 
import TysPrim


import Data.Default
import Data.Maybe (fromMaybe)


instance Default Type where
    def = TyVarTy alphaTyVar 
    
-- JP: Let's try to avoid this.
-- instance Default CoreExpr where 
--     def = Var $ mkVar (Just "undefined") 0 def

mkVar :: Maybe String -> Int -> Type -> Var
mkVar x i t = mkGlobalVar VanillaId name t vanillaIdInfo 
  where 
    name = mkSystemName (mkUnique 'S' i) (mkVarOcc x')
    x'   = fromMaybe (freshName i) x 

freshName :: Int -> String 
freshName i = "lSyn$" ++ show i 
