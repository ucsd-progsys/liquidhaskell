{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | This module contains the code that DOES reflection; i.e. converts Haskell
--   definitions into refinements.

module Language.Haskell.Liquid.Bare.Axiom ( makeHaskellAxioms, strengthenSpecWithMeasure, makeAssumeReflectAxioms, wiredReflects, AxiomType(..) ) where

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
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.CoreToLogic
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types

import           Language.Haskell.Liquid.Bare.Resolve as Bare
import           Language.Haskell.Liquid.Bare.Types   as Bare
import qualified Data.List as L
import Language.Haskell.Liquid.Misc (fst4)
import Control.Applicative
import Data.Function (on)
import qualified Data.Map as Map

findDuplicatePair :: Ord k => (a -> k) -> [a] -> Maybe (a, a)
findDuplicatePair key xs =
  Mb.listToMaybe
    [ (a, b)
    | a:b:_ <- L.groupBy ((==) `on` key) (L.sortOn key xs)
    ]

findDuplicateBetweenLists :: (Ord k) => (a -> k) -> [a] -> [a] -> Maybe (a, a)
findDuplicateBetweenLists key l1 l2 =
  findDuplicate key (Map.fromList [ (key x, x) | x <- l1 ]) l2
  where
    findDuplicate :: Ord k => (a -> k) -> Map.Map k a -> [a] -> Maybe (a, a)
    findDuplicate key' seen l2' =
      Mb.listToMaybe
      [ (x, y) | x <- l2', Just y <- [Map.lookup (key' x) seen]]

-----------------------------------------------------------------------------------------------
makeHaskellAxioms :: Config -> GhcSrc -> Bare.Env -> Bare.TycEnv -> ModName -> LogicMap -> GhcSpecSig -> Ms.BareSpec
                  -> Bare.Lookup [(Ghc.Var, LocSpecType, F.Equation)]
-----------------------------------------------------------------------------------------------
makeHaskellAxioms cfg src env tycEnv name lmap spSig spec = do
  wiDefs     <- wiredDefs cfg env name spSig
  let refDefs = getReflectDefs src spSig spec
  return (makeAxiom env tycEnv name lmap <$> (wiDefs ++ refDefs))

-----------------------------------------------------------------------------------------------
--          Returns a list of elements, one per assume reflect                               --
-- Each element is made of:                                                                  --
-- * The variable name of the actual function                                                --
-- * The refined type of actual function, where the post-condition is strengthened with      --
--   ``VV == pretendedFn arg1 arg2 ...`                                                      --
-- * The assume reflect equation, linking the pretended and actual function:                 --
--   `actualFn arg1 arg 2 ... = pretendedFn arg1 arg2 ...`                                   --
makeAssumeReflectAxioms :: GhcSrc -> Bare.Env -> Bare.TycEnv -> ModName -> GhcSpecSig -> Ms.BareSpec
                  -> Bare.Lookup [(Ghc.Var, LocSpecType, F.Equation)]
-----------------------------------------------------------------------------------------------
makeAssumeReflectAxioms src env tycEnv name spSig spec = do
  -- Send an error message if we're redefining a reflection
  case findDuplicatePair val reflActSymbols <|> findDuplicateBetweenLists val refSymbols reflActSymbols of
    Just (x , y) -> Ex.throw $ mkError y $ "Duplicate reflection of " ++ show x ++ " and " ++ show y
    Nothing -> return $ turnIntoAxiom <$> Ms.asmReflectSigs spec
  where
    turnIntoAxiom (actual, pretended) = makeAssumeReflectAxiom spSig env embs name (actual, pretended)
    refDefs                 = getReflectDefs src spSig spec
    embs                    = Bare.tcEmbs       tycEnv
    refSymbols              = fst4 <$> refDefs
    reflActSymbols          = fst <$> Ms.asmReflectSigs spec

-----------------------------------------------------------------------------------------------
-- Processes one `assume reflect` and returns its axiom element, as detailed in              --
-- `makeAssumeReflectAxioms`. Can also be used to compute the updated SpecType of            --
-- a type where we add the post-condition that actual and pretended are the same             --
makeAssumeReflectAxiom :: GhcSpecSig -> Bare.Env -> F.TCEmb Ghc.TyCon -> ModName
                       -> (LocSymbol, LocSymbol) -- actual function and pretended function
                       -> (Ghc.Var, LocSpecType, F.Equation)
-----------------------------------------------------------------------------------------------
makeAssumeReflectAxiom sig env tce name (actual, pretended) =
   -- The actual and pretended function must have the same type
  if pretendedTy == actualTy then
    (actualV, actual{val = aty at}, actualEq)
  else
    Ex.throw $ mkError actual $
      show qPretended ++ " and " ++ show qActual ++ " should have the same type. But " ++
      "types " ++ F.showpp pretendedTy ++ " and " ++ F.showpp actualTy  ++ " do not match."
  where
    at = val $ strengthenSpecWithMeasure sig env actualV pretended{val=qPretended}

    -- Get the Ghc.Var's of the actual and pretended function names
    actualV = case Bare.lookupGhcVar env name "assume-reflection" actual of
      Right x -> x
      Left _ -> Ex.throw $ mkError actual $ "Not in scope: " ++ show (val actual)
    pretendedV = case Bare.lookupGhcVar env name "assume-reflection" pretended of
      Right x -> x
      Left _ -> Ex.throw $ mkError pretended $ "Not in scope: " ++ show (val pretended)
    -- Get the qualified name symbols for the actual and pretended functions
    qActual = Bare.qualifyTop env name (F.loc actual) (val actual)
    qPretended = Bare.qualifyTop env name (F.loc pretended) (val pretended)
    -- Get the GHC type of the actual and pretended functions
    actualTy = Ghc.varType actualV
    pretendedTy = Ghc.varType pretendedV

    -- The return type of the function
    out   = rTypeSort tce $ ares at
    -- The arguments names and types, as given by `AxiomType`
    xArgs = fmap (rTypeSort tce) <$> aargs at

    -- Expression of the equation. It is just saying that the actual and pretended functions are the same
    -- when applied to the same arguments
    le    = foldl F.EApp (F.EVar qPretended) (F.EVar . fst <$> xArgs)

    actualEq = F.mkEquation qActual xArgs le out

strengthenSpecWithMeasure :: GhcSpecSig -> Bare.Env
                       -> Ghc.Var -- var owning the spec
                       -> LocSymbol     -- measure name
                       -> Located AxiomType
-----------------------------------------------------------------------------------------------
strengthenSpecWithMeasure sig env actualV qPretended =
    qPretended{ val = axiomType allowTC qPretended rt}
  where
    -- Get the GHC type of the actual and pretended functions
    actualTy = Ghc.varType actualV

    -- Compute the refined type of the actual function. See `makeAssumeType` for details
    sigs                    = gsTySigs sig ++ gsAsmSigs sig -- We also look into assumed signatures
    -- Try to get the specification of the actual function from the signatures
    mbT   = val <$> lookup actualV sigs
    -- Refines that spec. If the specification is not in the scope, just use the GHC type as a dummy spec
    -- to proceed with.
    rt    = fromRTypeRep .
            (\trep@RTypeRep{..} ->
                trep{ty_info = fmap (\i -> i{permitTC = Just allowTC}) ty_info}) .
            toRTypeRep $ Mb.fromMaybe (ofType actualTy) mbT
    allowTC = typeclass (getConfig env)

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
  Nothing     -> Ex.throw $ mkError x $ show (val x) ++ " is not in scope"

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
                trep{ty_info = fmap (\i -> i{permitTC = Just allowTC}) ty_info}) .
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
