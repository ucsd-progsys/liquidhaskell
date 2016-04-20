{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes     #-}

module Axiomatize where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

import Debug.Trace

import Control.Applicative
import Data.List ((\\))
import Data.Maybe (fromMaybe)

data Proof = Proof


{-@ auto :: Int -> b:{v:Bool |Prop v} -> Proof @-}
auto :: Int -> Bool -> Proof
auto _ _ = Proof


{-@ rewrite :: Int -> b:{v:Bool |Prop v} -> Proof @-}
rewrite :: Int -> Bool -> Proof
rewrite _ _ = Proof

{-@ cases :: Int -> b:{v:Bool |Prop v} -> Proof @-}
cases :: Int -> Bool -> Proof
cases _ _ = Proof


axiomatize :: Q [Dec] -> Q [Dec]
axiomatize q = do d <- q
                  let vts = [(x, t) | FunD x _ <- d, SigD y t <- d, x == y ]
                  ds <- mapM (axiomatizeOne vts) d
                  return $ concat ds

axiomatizeOne :: [(Name, Type)] -> Dec -> Q [Dec]
axiomatizeOne env f@(FunD name cs)
  = do axioms <- makeAxioms (lookup name env) name cs
       return $ f:axioms
axiomatizeOne _ (SigD _ _)
  = return []
axiomatizeOne _ d
  = error $ "axiomatizeOne: Cannot axiomatize" ++ show d

makeAxioms :: Maybe Type -> Name -> [Clause] -> Q [Dec]
makeAxioms t f cs = concat <$> mapM go cs
  where
    go :: Clause -> Q [Dec]
    go (Clause ps (NormalB (CaseE e ms)) []) = mapM (makeAxiomMatch f ps e) ms
    go (Clause ps (NormalB _) [])            = makeAxiomPattern t f ps
    go d = error $ "makeAxioms: Cannot axiomatize\n" ++ show d



makeAxiomPattern :: Maybe Type -> Name -> [Pat] -> Q [Dec]
makeAxiomPattern t g ps
  = do ifs <- mapM reify (fst <$> ds)
       ff <- makeFun f xs <$> axiom_body
       ft <- makeSigT t f ps
       return $ [ff] ++ ft
  where
    f = mkName $ makeNamePattern g (fst <$> ds)
    ds = [(n, dps) |  ConP n dps <- ps]
    xs = [x | VarP x <- (ps ++ concat (snd <$> ds))]

makeSigT Nothing _ _
  = return []
makeSigT (Just t) f ps
  = do r <- [t|Proof|]
       ifs <- mapM reify (fst . snd <$> ds)
       let ts2 = concat $ zipWith makePTys ds ifs
       return [SigD f $ mkUnivArrow (as, ts1 ++ ts2, r)]
  where
    (as, ts, _) = bkUnivFun t
    ts1 = [t | (t, VarP _) <- zip ts ps]
    ds  = [(t, (n, dps)) |  (t, ConP n dps) <- zip ts ps]

makePTys :: (Type, (Name, [Pat])) -> Info -> [Type]
makePTys (tr, (n, dps)) (DataConI m t _ _) | n == m
  = (applySub θ <$> [t | (t, VarP _) <- zip ts dps])
  where (as, ts, r) = bkUnivFun t
        θ = unify r tr
makePTys _ _ = error "makePTys: on invalid arguments"


unify (VarT n) t = [(n,t)]
unify t (VarT n) = [(n,t)]
unify (AppT t1 t2) (AppT t1' t2') = unify t1 t1' ++ unify t2 t2'
unify (ForallT _ _ t1) t2 = unify t1 t2
unify t1 (ForallT _ _ t2) = unify t1 t2
unify _ _  = []

applySub :: [(Name, Type)] -> Type -> Type
applySub θ t@(VarT v) = fromMaybe t (lookup v θ)
applySub θ (AppT t1 t2) = AppT (applySub θ t1) (applySub θ t2)
applySub θ (ForallT _ _ _) = error "applySub: TODO"
applySub θ t = t


bkUnivFun = go [] []
  where
    go as xs (ForallT vs _ t)   = go (as ++ vs) xs t
    go as xs (AppT (AppT ArrowT tx) t) = go as (tx:xs) t
    go as xs t                  = (as, reverse xs, t)

mkUnivArrow (as, ts, r) = ForallT as [] $ mkArrow ts r
  where
    mkArrow []     r = r
    mkArrow (t:ts) r = AppT (AppT ArrowT t) $ mkArrow ts r

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
