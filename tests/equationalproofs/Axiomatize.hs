{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Axiomatize where

import Language.Haskell.TH
import Language.Haskell.TH.Quote

import Debug.Trace

import Control.Applicative
import Data.List ((\\))


data Proof = Proof

axiomatize :: Q [Dec] -> Q [Dec]
axiomatize q = do d <- q
                  ds <- mapM axiomatizeOne d
                  return $ trace (show d) $ concat ds

axiomatizeOne :: Dec -> Q [Dec]
axiomatizeOne f@(FunD name cs)
  = do axioms <- makeAxioms name cs
       return $ f:axioms
axiomatizeOne d
  = error $ "axiomatizeOne: Cannot axiomatize" ++ show d

makeAxioms :: Name -> [Clause] -> Q [Dec]
makeAxioms f cs = concat <$> mapM go cs
  where
    go :: Clause -> Q [Dec]
    go (Clause ps (NormalB (CaseE e ms)) []) = mapM (makeAxiomMatch f ps e) ms
    go (Clause ps (NormalB _) [])            = (\x -> [x]) <$> makeAxiomPattern f ps
    go d = error $ "makeAxioms: Cannot axiomatize\n" ++ show d



makeAxiomPattern :: Name -> [Pat] -> Q Dec
makeAxiomPattern g ps = makeFun f xs <$> axiom_body
  where
    f = mkName $ makeNamePattern g (fst <$> ds)
    ds = [(n, dps) |  ConP n dps <- ps]
    xs = [x | VarP x <- (ps ++ concat (snd <$> ds))]


makeAxiomMatch :: Name -> [Pat] -> Exp -> Match -> Q Dec
makeAxiomMatch g ps (VarE x) (Match (ConP dc dps) bd decs)
  = makeFun f xs <$> axiom_body
  where f  = mkName $ makeName g x dc
        xs = [p | VarP p <- ps ++ dps] \\ [x]

makeFun :: Name -> [Name] -> Exp -> Dec
makeFun f xs bd = FunD f [Clause (VarP <$> xs) (NormalB bd) []]

axiom_body :: Q Exp
axiom_body = [|Proof|]

sep = "_"
mkSep :: [String] -> String
mkSep []  = []
mkSep [x] = x
mkSep (x:xs) = x ++ sep ++ mkSep xs

eq  = "is"
makeName fname x dc
  = mkSep ["axiom", nameBase fname, nameBase x, eq, nameBase dc]

makeNamePattern fname dcs = mkSep $ ["axiom", nameBase fname] ++ (nameBase <$> dcs)
