{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | This module contains the code that DOES reflection; i.e. converts Haskell
--   definitions into refinements.

module Language.Haskell.Liquid.Bare.Axiom ( makeHaskellAxioms, wiredReflects ) where

import Prelude hiding (error)
import Prelude hiding (mapM)
import qualified Control.Exception         as Ex

-- import           Control.Monad.Except      hiding (forM, mapM)
-- import           Control.Monad.State       hiding (forM, mapM)
import qualified Text.PrettyPrint.HughesPJ as PJ -- (text)
import qualified Data.HashSet              as S
import qualified Data.Maybe                as Mb
import Control.Monad.Trans.State.Lazy (runState, get, put)

import           Language.Fixpoint.Misc
import qualified Language.Haskell.Liquid.Measure as Ms
import qualified Language.Fixpoint.Types as F
import qualified Liquid.GHC.API as Ghc
import qualified Liquid.GHC.Misc as GM
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.CoreToLogic
import           Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types

import           Language.Haskell.Liquid.Bare.Resolve as Bare
import           Language.Haskell.Liquid.Bare.Types   as Bare

-----------------------------------------------------------------------------------------------
makeHaskellAxioms :: Config -> GhcSrc -> Bare.Env -> Bare.TycEnv -> ModName -> LogicMap -> GhcSpecSig -> Ms.BareSpec
                  -> Bare.Lookup [(Ghc.Var, LocSpecType, F.Equation)]
-----------------------------------------------------------------------------------------------
makeHaskellAxioms cfg src env tycEnv name lmap spSig spec = do
  wiDefs     <- wiredDefs cfg env name spSig
  let refDefs = getReflectDefs src spSig spec
  return (makeAxiom env tycEnv name lmap <$> (wiDefs ++ refDefs))

getReflectDefs :: GhcSrc -> GhcSpecSig -> Ms.BareSpec
               -> [(LocSymbol, Maybe SpecType, Ghc.Var, Ghc.CoreExpr)]
getReflectDefs src sig spec = findVarDefType cbs sigs <$> xs
  where
    sigs                    = gsTySigs sig
    xs                      = S.toList (Ms.reflects spec)
    cbs                     = _giCbs src

findVarDefType :: [Ghc.CoreBind] -> [(Ghc.Var, LocSpecType)] -> LocSymbol
               -> (LocSymbol, Maybe SpecType, Ghc.Var, Ghc.CoreExpr)
findVarDefType cbs sigs x = case findVarDefMethod (val x) cbs of
  -- YL: probably ok even without checking typeclass flag since user cannot
  -- manually reflect internal names
  Just (v, e) -> if GM.isExternalId v || isMethod (F.symbol x) || isDictionary (F.symbol x)
                   then (x, val <$> lookup v sigs, v, e)
                   else Ex.throw $ mkError x ("Lifted functions must be exported; please export " ++ show v)
  Nothing     -> Ex.throw $ mkError x "Cannot lift haskell function"

--------------------------------------------------------------------------------
makeAxiom :: Bare.Env -> Bare.TycEnv -> ModName -> LogicMap
          -> (LocSymbol, Maybe SpecType, Ghc.Var, Ghc.CoreExpr)
          -> (Ghc.Var, LocSpecType, F.Equation)
--------------------------------------------------------------------------------
makeAxiom env tycEnv name lmap (x, mbT, v, def)
            = (v, t, e)
  where
    t       = Bare.qualifyTop env name (F.loc t0) t0
    (t0, e) = makeAssumeType allowTC embs lmap dm x mbT v def
    embs    = Bare.tcEmbs       tycEnv
    dm      = Bare.tcDataConMap tycEnv
    allowTC = typeclass (getConfig env)

mkError :: LocSymbol -> String -> Error
mkError x str = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (PJ.text str)

makeAssumeType
  :: Bool -- ^ typeclass enabled
  -> F.TCEmb Ghc.TyCon -> LogicMap -> DataConMap -> LocSymbol -> Maybe SpecType
  -> Ghc.Var -> Ghc.CoreExpr
  -> (LocSpecType, F.Equation)
makeAssumeType allowTC tce lmap dm sym mbT v def
  = (sym {val = aty at `strengthenRes` F.subst su ref},  F.mkEquation (val sym) xts (F.subst su le) out)
  where
    rt    = fromRTypeRep .
            (\trep@RTypeRep{..} ->
                trep{ty_info = fmap (\rinfo -> rinfo{permitTC = Just allowTC}) ty_info}) .
            toRTypeRep $ Mb.fromMaybe (ofType τ) mbT
    τ     = Ghc.varType v
    at    = axiomType allowTC sym rt
    out   = rTypeSort tce $ ares at
    xArgs = F.EVar . fst <$> aargs at
    _msg  = unwords [showpp sym, showpp mbT]
    le    = case runToLogicWithBoolBinds bbs tce lmap dm mkErr (coreToLogic allowTC def') of
              Right e -> e
              Left  e -> panic Nothing (show e)
    ref        = F.Reft (F.vv_, F.PAtom F.Eq (F.EVar F.vv_) le)
    mkErr s    = ErrHMeas (sourcePosSrcSpan $ loc sym) (pprint $ val sym) (PJ.text s)
    bbs        = filter isBoolBind xs
    (xs, def') = GM.notracePpr "grabBody" $ grabBody allowTC (Ghc.expandTypeSynonyms τ) $ normalize allowTC def
    su         = F.mkSubst  $ zip (F.symbol     <$> xs) xArgs
                           ++ zip (simplesymbol <$> xs) xArgs
    xts        = [(F.symbol x, rTypeSortExp tce t) | (x, t) <- aargs at]

rTypeSortExp :: F.TCEmb Ghc.TyCon -> SpecType -> F.Sort
rTypeSortExp tce = typeSort tce . Ghc.expandTypeSynonyms . toType False

grabBody :: Bool -- ^ typeclass enabled
         -> Ghc.Type -> Ghc.CoreExpr -> ([Ghc.Var], Ghc.CoreExpr)
grabBody allowTC (Ghc.ForAllTy _ ty) e
  = grabBody allowTC ty e
grabBody allowTC@False Ghc.FunTy{ Ghc.ft_arg = tx, Ghc.ft_res = t} e | Ghc.isClassPred tx
  = grabBody allowTC t e
grabBody allowTC@True Ghc.FunTy{ Ghc.ft_arg = tx, Ghc.ft_res = t} e | isEmbeddedDictType tx
  = grabBody allowTC t e
grabBody allowTC torig@Ghc.FunTy {} (Ghc.Let (Ghc.NonRec x e) body)
  = grabBody allowTC torig (subst (x,e) body)
grabBody allowTC Ghc.FunTy{ Ghc.ft_res = t} (Ghc.Lam x e)
  = (x:xs, e') where (xs, e') = grabBody allowTC t e
grabBody allowTC t (Ghc.Tick _ e)
  = grabBody allowTC t e
grabBody allowTC ty@Ghc.FunTy{} e
  = (txs++xs, e')
   where (ts,tr)  = splitFun ty
         (xs, e') = grabBody allowTC tr (foldl Ghc.App e (Ghc.Var <$> txs))
         txs      = [ stringVar ("ls" ++ show i) t |  (t,i) <- zip ts [(1::Int)..]]
grabBody _ _ e
  = ([], e)

splitFun :: Ghc.Type -> ([Ghc.Type], Ghc.Type)
splitFun = go []
  where go acc Ghc.FunTy{ Ghc.ft_arg = tx, Ghc.ft_res = t} = go (tx:acc) t
        go acc t                                           = (reverse acc, t)


isBoolBind :: Ghc.Var -> Bool
isBoolBind v = isBool (ty_res $ toRTypeRep ((ofType $ Ghc.varType v) :: RRType ()))

strengthenRes :: SpecType -> F.Reft -> SpecType
strengthenRes st rf = go st
  where
    go (RAllT a t r)   = RAllT a (go t) r
    go (RAllP p t)     = RAllP p $ go t
    go (RFun x i tx t r) = RFun x i tx (go t) r
    go t               =  t `strengthen` F.ofReft rf

class Subable a where
  subst :: (Ghc.Var, Ghc.CoreExpr) -> a -> a

instance Subable Ghc.Var where
  subst (x, ex) z
    | x == z, Ghc.Var y <- ex = y
    | otherwise           = z

instance Subable Ghc.CoreExpr where
  subst (x, ex) (Ghc.Var y)
    | x == y    = ex
    | otherwise = Ghc.Var y
  subst su (Ghc.App f e)
    = Ghc.App (subst su f) (subst su e)
  subst su (Ghc.Lam x e)
    = Ghc.Lam x (subst su e)
  subst su (Ghc.Case e x t alts)
    = Ghc.Case (subst su e) x t (subst su <$> alts)
  subst su (Ghc.Let (Ghc.Rec xes) e)
    = Ghc.Let (Ghc.Rec (mapSnd (subst su) <$> xes)) (subst su e)
  subst su (Ghc.Let (Ghc.NonRec x ex) e)
    = Ghc.Let (Ghc.NonRec x (subst su ex)) (subst su e)
  subst su (Ghc.Cast e t)
    = Ghc.Cast (subst su e) t
  subst su (Ghc.Tick t e)
    = Ghc.Tick t (subst su e)
  subst _ e
    = e

instance Subable Ghc.CoreAlt where
  subst su (Ghc.Alt c xs e) = Ghc.Alt c xs (subst su e)

data AxiomType = AT { aty :: SpecType, aargs :: [(F.Symbol, SpecType)], ares :: SpecType }

-- | Specification for Haskell function
axiomType :: Bool -> LocSymbol -> SpecType -> AxiomType
axiomType allowTC s st = AT to (reverse xts) res
  where
    (to, (_,xts, Just res)) = runState (go st) (1,[], Nothing)
    go (RAllT a t r) = RAllT a <$> go t <*> return r
    go (RAllP p t) = RAllP p <$> go t
    go (RFun x i tx t r) | isErasable tx = (\t' -> RFun x i tx t' r) <$> go t
    go (RFun x ii tx t r) = do
      (i,bs,mres) <- get
      let x' = unDummy x i
      put (i+1, (x', tx):bs,mres)
      t' <- go t
      return $ RFun x' ii tx t' r
    go t = do
      (i,bs,_) <- get
      let ys = reverse $ map fst bs
      let t' = strengthen t (singletonApp s ys)
      put (i, bs, Just t')
      return t'
    isErasable = if allowTC then isEmbeddedClass else isClassType
unDummy :: F.Symbol -> Int -> F.Symbol
unDummy x i
  | x /= F.dummySymbol = x
  | otherwise          = F.symbol ("lq" ++ show i)

singletonApp :: F.Symbolic a => LocSymbol -> [a] -> UReft F.Reft
singletonApp s ys = MkUReft r mempty
  where
    r             = F.exprReft (F.mkEApp s (F.eVar <$> ys))


-------------------------------------------------------------------------------
-- | Hardcode imported reflected functions ------------------------------------
-------------------------------------------------------------------------------

wiredReflects :: Config -> Bare.Env -> ModName -> GhcSpecSig ->
                 Bare.Lookup [Ghc.Var]
wiredReflects cfg env name sigs = do
  vs <- wiredDefs cfg env name sigs
  return [v | (_, _, v, _) <- vs]

wiredDefs :: Config -> Bare.Env -> ModName -> GhcSpecSig
          -> Bare.Lookup [(LocSymbol, Maybe SpecType, Ghc.Var, Ghc.CoreExpr)]
wiredDefs cfg env name spSig
  | reflection cfg = do
    let x = F.dummyLoc functionComposisionSymbol
    v    <- Bare.lookupGhcVar env name "wiredAxioms" x
    return [ (x, F.val <$> lookup v (gsTySigs spSig), v, makeCompositionExpression v) ]
  | otherwise =
    return []

-------------------------------------------------------------------------------
-- | Expression Definitions of Prelude Functions ------------------------------
-- | NV: Currently Just Hacking Composition       -----------------------------
-------------------------------------------------------------------------------


makeCompositionExpression :: Ghc.Id -> Ghc.CoreExpr
makeCompositionExpression gid
  =  go $ Ghc.varType $ F.notracepp ( -- tracing to find  the body of . from the inline spec, 
                                      -- replace F.notrace with F.trace to print 
      "\nv = " ++ GM.showPpr gid ++
      "\n realIdUnfolding = " ++ GM.showPpr (Ghc.realIdUnfolding gid) ++
      "\n maybeUnfoldingTemplate . realIdUnfolding = " ++ GM.showPpr (Ghc.maybeUnfoldingTemplate $ Ghc.realIdUnfolding gid ) ++
      "\n inl_src . inlinePragInfo . Ghc.idInfo = "    ++ GM.showPpr (Ghc.inl_src $ Ghc.inlinePragInfo $ Ghc.idInfo gid) ++
      "\n inl_inline . inlinePragInfo . Ghc.idInfo = " ++ GM.showPpr (Ghc.inl_inline $ Ghc.inlinePragInfo $ Ghc.idInfo gid) ++
      "\n inl_sat . inlinePragInfo . Ghc.idInfo = "    ++ GM.showPpr (Ghc.inl_sat $ Ghc.inlinePragInfo $ Ghc.idInfo gid) ++
      "\n inl_act . inlinePragInfo . Ghc.idInfo = "    ++ GM.showPpr (Ghc.inl_act $ Ghc.inlinePragInfo $ Ghc.idInfo gid) ++
      "\n inl_rule . inlinePragInfo . Ghc.idInfo = "   ++ GM.showPpr (Ghc.inl_rule $ Ghc.inlinePragInfo $ Ghc.idInfo gid) ++
      "\n inl_rule rule = " ++ GM.showPpr (Ghc.inl_rule $ Ghc.inlinePragInfo $ Ghc.idInfo gid) ++
      "\n inline spec = " ++ GM.showPpr (Ghc.inl_inline $ Ghc.inlinePragInfo $ Ghc.idInfo gid)
     ) gid
   where
    go (Ghc.ForAllTy a (Ghc.ForAllTy b (Ghc.ForAllTy c Ghc.FunTy{ Ghc.ft_arg = tf, Ghc.ft_res = Ghc.FunTy { Ghc.ft_arg = tg, Ghc.ft_res = tx}})))
      = let f = stringVar "f" tf
            g = stringVar "g" tg
            x = stringVar "x" tx
        in Ghc.Lam (Ghc.binderVar a) $
           Ghc.Lam (Ghc.binderVar b) $
           Ghc.Lam (Ghc.binderVar c) $
           Ghc.Lam f $ Ghc.Lam g $ Ghc.Lam x $ Ghc.App (Ghc.Var f) (Ghc.App (Ghc.Var g) (Ghc.Var x))
    go _ = error "Axioms.go"
