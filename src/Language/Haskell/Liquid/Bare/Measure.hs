{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Measure (
    makeHaskellMeasures
  , makeHaskellInlines
  , makeHaskellBounds
  , makeMeasureSpec
  , makeMeasureSpec'
  , makeClassMeasureSpec
  , makeMeasureSelectors
  , strengthenHaskellMeasures
  , varMeasures
  ) where

import CoreSyn
import DataCon
import Id
import Name
import Type hiding (isFunTy)
import Var

import Prelude hiding (mapM)
import Control.Arrow ((&&&))
import Control.Applicative ((<$>), (<*>))
import Control.Monad hiding (forM, mapM)
import Control.Monad.Error hiding (Error, forM, mapM)
import Control.Monad.State hiding (forM, mapM)
import Data.Bifunctor
import Data.Maybe
import Data.Char (toUpper)
import Data.Monoid
import Data.Traversable (forM, mapM)
import Text.PrettyPrint.HughesPJ (text)
import Text.Parsec.Pos (SourcePos)

import qualified Data.List as L

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import Language.Fixpoint.Misc (mlookup, sortNub)
import Language.Fixpoint.Types (Symbol, dummySymbol, symbolString, symbol, Expr(..))
import Language.Fixpoint.SortCheck (isFirstOrder)

import qualified Language.Fixpoint.Types as F

import Language.Haskell.Liquid.Transforms.CoreToLogic
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GHC.Misc (dropModuleNames, getSourcePos, getSourcePosE, sourcePosSrcSpan, isDataConId)
import Language.Haskell.Liquid.Types.RefType (dataConSymbol, generalize, ofType, uRType, typeSort)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.Bounds

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Misc       (simpleSymbolVar, hasBoolResult)
import Language.Haskell.Liquid.Bare.Expand
import Language.Haskell.Liquid.Bare.Lookup
import Language.Haskell.Liquid.Bare.OfType
import Language.Haskell.Liquid.Bare.Resolve
import Language.Haskell.Liquid.Bare.RefToLogic

makeHaskellMeasures :: [CoreBind] -> ModName -> (ModName, Ms.BareSpec) -> BareM (Ms.MSpec SpecType DataCon)
makeHaskellMeasures _   name' (name, _   ) | name /= name'
  = return mempty
makeHaskellMeasures cbs _     (_   , spec)
  = do lmap <- gets logicEnv
       Ms.mkMSpec' <$> mapM (makeMeasureDefinition lmap cbs') (S.toList $ Ms.hmeas spec)
  where
    cbs'                  = concatMap unrec cbs
    unrec cb@(NonRec _ _) = [cb]
    unrec (Rec xes)       = [NonRec x e | (x, e) <- xes]

makeHaskellInlines :: [CoreBind] -> ModName -> (ModName, Ms.BareSpec) -> BareM ()
makeHaskellInlines _   name' (name, _   ) | name /= name'
  = return mempty
makeHaskellInlines cbs _     (_   , spec)
  = do lmap <- gets logicEnv
       mapM_ (makeMeasureInline lmap cbs') (S.toList $ Ms.inlines spec)
  where
    cbs'                  = concatMap unrec cbs
    unrec cb@(NonRec _ _) = [cb]
    unrec (Rec xes)       = [NonRec x e | (x, e) <- xes]

makeMeasureInline :: LogicMap -> [CoreBind] ->  LocSymbol -> BareM ()
makeMeasureInline lmap cbs  x
  = case filter ((val x `elem`) . map (dropModuleNames . simplesymbol) . binders) cbs of
    (NonRec v def:_)   -> do {e <- coreToFun' x v def; updateInlines x e}
    (Rec [(v, def)]:_) -> do {e <- coreToFun' x v def; updateInlines x e}
    _                  -> throwError $ mkError "Cannot inline haskell function"
  where
    binders (NonRec z _) = [z]
    binders (Rec xes)    = fst <$> xes

    coreToFun' x v def = case runToLogic lmap mkError $ coreToFun x v def of
                           Left (xs, e)  -> return (TI (symbol <$> xs) e)
                           Right e -> throwError e

    mkError :: String -> Error
    mkError str = ErrHMeas (sourcePosSrcSpan $ loc x) (val x) (text str)


updateInlines x v = modify $ \s -> let iold  = M.insert (val x) v (inlines s) in
                                   s{inlines = M.map (f iold) iold }
  where
    f             = txRefToLogic mempty

makeMeasureDefinition :: LogicMap -> [CoreBind] -> LocSymbol -> BareM (Measure SpecType DataCon)
makeMeasureDefinition lmap cbs x
  = case filter ((val x `elem`) . map (dropModuleNames . simplesymbol) . binders) cbs of
    (NonRec v def:_)   -> Ms.mkM x (logicType $ varType v) <$> coreToDef' x v def
    (Rec [(v, def)]:_) -> Ms.mkM x (logicType $ varType v) <$> coreToDef' x v def
    _                  -> throwError $ mkError "Cannot extract measure from haskell function"
  where
    binders (NonRec x _) = [x]
    binders (Rec xes)    = fst <$> xes

    coreToDef' x v def = case runToLogic lmap mkError $ coreToDef x v def of
                           Left l  -> return     l
                           Right e -> throwError e

    mkError :: String -> Error
    mkError str = ErrHMeas (sourcePosSrcSpan $ loc x) (val x) (text str)

simplesymbol :: CoreBndr -> Symbol
simplesymbol = symbol . getName

strengthenHaskellMeasures :: S.HashSet (Located Var) -> [(Var, Located SpecType)]
strengthenHaskellMeasures hmeas
  = (val &&& fmap strengthenResult) <$> S.toList hmeas

makeMeasureSelectors :: (DataCon, Located DataConP) -> [Measure SpecType DataCon]
makeMeasureSelectors (dc, Loc l l' (DataConP _ vs _ _ _ xts r _))
  = catMaybes (go <$> zip (reverse xts) [1..])
  where
    go ((x,t), i)
      | isFunTy t = Nothing
      | otherwise = Just $ makeMeasureSelector (Loc l l' x) (dty t) dc n i

    dty t         = foldr RAllT  (RFun dummySymbol r (fmap mempty t) mempty) vs
    n             = length xts

makeMeasureSelector x s dc n i = M {name = x, sort = s, eqns = [eqn]}
  where eqn   = Def x [] dc Nothing (((, Nothing) . mkx) <$> [1 .. n]) (E (EVar $ mkx i))
        mkx j = symbol ("xx" ++ show j)


makeMeasureSpec :: (ModName, Ms.Spec BareType LocSymbol) -> BareM (Ms.MSpec SpecType DataCon)
makeMeasureSpec (mod,spec) = inModule mod mkSpec
  where
    mkSpec = mkMeasureDCon =<< mkMeasureSort =<< m
    m      = Ms.mkMSpec <$> mapM expandMeasure (Ms.measures spec)
                        <*> return (Ms.cmeasures spec)
                        <*> mapM expandMeasure (Ms.imeasures spec)

makeMeasureSpec' = mapFst (mapSnd uRType <$>) . Ms.dataConTypes . first (mapReft ur_reft)

makeClassMeasureSpec (Ms.MSpec {..}) = tx <$> M.elems cmeasMap
  where
    tx (M n s _) = (n, CM n (mapReft ur_reft s) -- [(t,m) | (IM n' t m) <- imeas, n == n']
                   )


mkMeasureDCon :: Ms.MSpec t LocSymbol -> BareM (Ms.MSpec t DataCon)
mkMeasureDCon m
  = mkMeasureDCon_ m <$> forM (measureCtors m)
                           (\n -> (val n,) <$> lookupGhcDataCon n)

mkMeasureDCon_ :: Ms.MSpec t LocSymbol -> [(Symbol, DataCon)] -> Ms.MSpec t DataCon
mkMeasureDCon_ m ndcs = m' {Ms.ctorMap = cm'}
  where
    m'  = fmap (tx.val) m
    cm' = hashMapMapKeys (tx' . tx) $ Ms.ctorMap m'
    tx  = mlookup (M.fromList ndcs)
    tx' = dataConSymbol

measureCtors ::  Ms.MSpec t LocSymbol -> [LocSymbol]
measureCtors = sortNub . fmap ctor . concat . M.elems . Ms.ctorMap

mkMeasureSort ::  Ms.MSpec BareType LocSymbol -> BareM (Ms.MSpec SpecType LocSymbol)
mkMeasureSort (Ms.MSpec c mm cm im)
  = Ms.MSpec <$> forM c (mapM txDef) <*> forM mm tx <*> forM cm tx <*> forM im tx
    where
      tx :: Measure BareType ctor -> BareM (Measure SpecType ctor)
      tx (M n s eqs) = M n <$> ofMeaSort s <*> mapM txDef eqs

      txDef :: Def BareType ctor -> BareM (Def SpecType ctor)
      txDef def = liftM3 (\xs t bds-> def{ dparams = xs, dsort = t, binds = bds})
                  (mapM (mapSndM ofMeaSort) (dparams def))
                  (mapM ofMeaSort $ dsort def)
                  (mapM (mapSndM $ mapM ofMeaSort) (binds def))


varMeasures :: (Monoid r) => [Var] -> [(Symbol, Located (RRType r))]
varMeasures vars = [ (symbol v, varSpecType v)  | v <- vars
                                                , isDataConId v
                                                , isSimpleType $ varType v ]

isSimpleType :: Type -> Bool
isSimpleType = isFirstOrder . typeSort M.empty

-- OLD isSimpleType t   = null tvs && isNothing (splitFunTy_maybe tb)
-- OLD  where
-- OLD    (tvs, tb)    = splitForAllTys t

varSpecType :: (Monoid r) => Var -> Located (RRType r)
varSpecType v    = Loc l l' (ofType $ varType v)
  where
    l            = getSourcePos  v
    l'           = getSourcePosE v


makeHaskellBounds :: CoreProgram -> S.HashSet (Var, LocSymbol) -> BareM RBEnv
makeHaskellBounds cbs xs
  = do lmap <- gets logicEnv
       M.fromList <$> mapM (makeHaskellBound lmap cbs) (S.toList xs)


makeHaskellBound lmap  cbs (v, x) = case filter ((v  `elem`) . binders) cbs of
    (NonRec v def:_)   -> do {e <- coreToFun' x v def; return $ toBound v x e}
    (Rec [(v, def)]:_) -> do {e <- coreToFun' x v def; return $ toBound v x e}
    _                  -> throwError $ mkError "Cannot make bound of haskell function"

  where
    binders (NonRec x _) = [x]
    binders (Rec xes)    = fst <$> xes

    coreToFun' x v def = case runToLogic lmap mkError $ coreToFun x v def of
                           Left (xs, e) -> return (xs, e)
                           Right e      -> throwError e

    mkError :: String -> Error
    mkError str = ErrHMeas (sourcePosSrcSpan $ loc x) (val x) (text str)


toBound :: Var -> LocSymbol -> ([Var], Either F.Pred F.Expr) -> (LocSymbol, RBound)
toBound v x (vs, Left p) = (x', Bound x' fvs ps xs p)
  where
    x'         = capitalizeBound x
    (ps', xs') = L.partition (hasBoolResult . varType) vs
    (ps , xs)  = (txp <$> ps', txx <$> xs')
    txp v      = (dummyLoc $ simpleSymbolVar v, ofType $ varType v)
    txx v      = (dummyLoc $ symbol v,          ofType $ varType v)
    fvs        = (((`RVar` mempty) . RTV) <$> fst (splitForAllTys $ varType v)) :: [RSort]

toBound v x (vs, Right e) = toBound v x (vs, Left $ F.PBexp e)

capitalizeBound = fmap (symbol . toUpperHead . symbolString)
  where
    toUpperHead []     = []
    toUpperHead (x:xs) = toUpper x:xs

--------------------------------------------------------------------------------
-- | Expand Measures -----------------------------------------------------------
--------------------------------------------------------------------------------

expandMeasure m
  = do eqns <- sequence $ expandMeasureDef <$> eqns m
       return $ m { sort = generalize (sort m)
                  , eqns = eqns }

expandMeasureDef :: Def t LocSymbol -> BareM (Def t LocSymbol)
expandMeasureDef d
  = do body <- expandMeasureBody (loc $ measure d) $ body d
       return $ d { body = body }

expandMeasureBody :: SourcePos -> Body -> BareM Body
expandMeasureBody l (P p)   = P   <$> (resolve l =<< expandPred p)
expandMeasureBody l (R x p) = R x <$> (resolve l =<< expandPred p)
expandMeasureBody l (E e)   = E   <$> resolve l e
