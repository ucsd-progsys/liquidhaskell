{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Haskell.Liquid.Quasi where

import Data.Either.Located
import Text.Parsec.Pos

import Language.Fixpoint.Types.Names
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Types
-- import Language.Haskell.Liquid.Types.RefType

-- import qualified GHC
import qualified Language.Haskell.TH as TH

specToType :: LocBareType -> TH.Type
specToType = typeToTH . val
  where
    typeToTH :: BareType -> TH.Type
    typeToTH = \case
      RVar a _
        -> TH.VarT (tvToTH a)
      RFun _ i o _
        -> TH.AppT (TH.AppT TH.ArrowT (typeToTH i)) (typeToTH o)
      RAllT RTVar{ty_var_value} t
        -> TH.ForallT [TH.PlainTV (tvToTH ty_var_value)] [] (typeToTH t)
      RApp BTyCon{btc_tc} ts _ _
        -> foldl TH.AppT
             (TH.ConT (TH.mkName (symbolString (val btc_tc))))
             (map typeToTH ts)
      RAppTy t s _
        -> TH.AppT (typeToTH t) (typeToTH s)
      t -> error ("Unexpected: " ++ show t)

    tvToTH :: BTyVar -> TH.Name
    tvToTH (BTV a) = TH.mkName (symbolString a)

specToAnn :: LocBareType -> TH.ExpQ
specToAnn = typeToAnn . val
  where
    typeToAnn :: BareType -> TH.ExpQ
    typeToAnn = \case
      RVar _a r
        -> [| RHole r |]
      RFun v i o r
        -> [| RFun v $(typeToAnn i) $(typeToAnn o) r |]
      RAllT _ t
        -> typeToAnn t
      RApp c ts ps r
        -> [| RApp c $(TH.listE $ map typeToAnn ts) ps r |]
      RAppTy t s r
        -> [| RAppTy $(typeToAnn t) $(typeToAnn s) r |]
      t -> error ("Unexpected: " ++ show t)


test1 :: (LocSymbol, LocBareType)
test1 = case fromRight $ singleSpecP testLoc "id :: x:a -> {v:a | v = x}" of
  Asrt sp -> sp
  Asrts ([var], (ty, _)) -> (var, ty)
  sp -> error ("Unexpected: " ++ show sp)

testLoc :: SourcePos
testLoc = initialPos "<test>"
