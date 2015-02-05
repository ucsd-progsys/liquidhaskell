{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Measure (
    makeHaskellMeasures
  , makeHaskellInlines

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
import Type
import Var

import Control.Applicative ((<$>), (<*>))
import Control.Monad hiding (forM)
import Control.Monad.Error hiding (Error, forM)
import Control.Monad.State hiding (forM)
import Data.Bifunctor
import Data.Maybe
import Data.Monoid
import Data.Traversable (forM)
import Text.PrettyPrint.HughesPJ (text)
import Text.Parsec.Pos (SourcePos)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import Language.Fixpoint.Misc (hashMapMapKeys, mapFst, mapSnd, mlookup, sortNub, traceShow)
import Language.Fixpoint.Names (dropModuleNames, dummySymbol)
import Language.Fixpoint.Types (Expr(..), Symbol, symbol)

import Language.Haskell.Liquid.CoreToLogic
import Language.Haskell.Liquid.GhcMisc (getSourcePos, sourcePosSrcSpan)
import Language.Haskell.Liquid.RefType (dataConSymbol, generalize, ofType, uRType)
import Language.Haskell.Liquid.Types

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Expand
import Language.Haskell.Liquid.Bare.Lookup
import Language.Haskell.Liquid.Bare.OfType
import Language.Haskell.Liquid.Bare.Resolve
import Language.Haskell.Liquid.Bare.RefToLogic

import Debug.Trace (trace)

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
       mapM_ (makeMeasureInline lmap cbs')  (traceShow "INLINES" $ S.toList $ Ms.inlines spec) 
  where 
    cbs'                  = concatMap unrec cbs
    unrec cb@(NonRec _ _) = [cb]
    unrec (Rec xes)       = [NonRec x e | (x, e) <- xes]


makeMeasureInline :: LogicMap -> [CoreBind] ->  LocSymbol -> BareM ()
makeMeasureInline lmap cbs  x 
  = case (filter ((val x `elem`) . (map (dropModuleNames . simplesymbol)) . binders) cbs) of
    (NonRec v def:_)   -> do {e <- coreToFun' x v def; updateInlines x e}
    (Rec [(v, def)]:_) -> do {e <- coreToFun' x v def; updateInlines x e}
    _                  -> throwError $ mkError "Cannot inline haskell function"
  where
    binders (NonRec x _) = [x]
    binders (Rec xes)    = fst <$> xes  

    coreToFun' x v def = case (runToLogic lmap mkError $ coreToFun x v def) of 
                           Left (xs, e)  -> return (TI xs e)
                           Right e -> throwError e

    mkError :: String -> Error
    mkError str = ErrHMeas (sourcePosSrcSpan $ loc x) (val x) (text str)         



updateInlines x v = modify $ \s -> let iold  = M.insert (val x) v (inlines s) in 
                                   s{inlines = M.map (f iold) iold }
  where f imap = txRefToLogic mempty imap 


makeMeasureDefinition :: LogicMap -> [CoreBind] -> LocSymbol -> BareM (Measure SpecType DataCon)
makeMeasureDefinition lmap cbs x 
  = case (filter ((val x `elem`) . (map (dropModuleNames . simplesymbol)) . binders) cbs) of
    (NonRec v def:_)   -> (Ms.mkM x (logicType $ varType v)) <$> coreToDef' x v def
    (Rec [(v, def)]:_) -> (Ms.mkM x (logicType $ varType v)) <$> coreToDef' x v def
    _                  -> throwError $ mkError "Cannot extract measure from haskell function"
  where
    binders (NonRec x _) = [x]
    binders (Rec xes)    = fst <$> xes  

    coreToDef' x v def = case (runToLogic lmap mkError $ coreToDef x v def) of 
                           Left l  -> return  l
                           Right e -> throwError e

    mkError :: String -> Error
    mkError str = ErrHMeas (sourcePosSrcSpan $ loc x) (val x) (text str)         

simplesymbol = symbol . getName


strengthenHaskellMeasures :: S.HashSet Var -> [(Var, Located SpecType)]
strengthenHaskellMeasures hmeas = (\v -> (v, dummyLoc $ strengthenResult v)) <$> (S.toList hmeas)

makeMeasureSelectors :: (DataCon, Located DataConP) -> [Measure SpecType DataCon]
makeMeasureSelectors (dc, (Loc loc (DataConP _ vs _ _ _ xts r))) = go <$> zip (reverse xts) [1..]
  where
    go ((x,t), i) = makeMeasureSelector (Loc loc x) (dty t) dc n i
        
    dty t         = foldr RAllT  (RFun dummySymbol r (fmap mempty t) mempty) vs
    n             = length xts

makeMeasureSelector x s dc n i = M {name = x, sort = s, eqns = [eqn]}
  where eqn   = Def x dc (mkx <$> [1 .. n]) (E (EVar $ mkx i)) 
        mkx j = symbol ("xx" ++ show j)


makeMeasureSpec :: (ModName, Ms.Spec BareType LocSymbol) -> BareM (Ms.MSpec SpecType DataCon)
makeMeasureSpec (mod,spec) = inModule mod mkSpec
  where
    mkSpec = mkMeasureDCon =<< mkMeasureSort =<< m
    m      = Ms.mkMSpec <$> (mapM expandMeasure $ Ms.measures spec)
                        <*> return (Ms.cmeasures spec)
                        <*> (mapM expandMeasure $ Ms.imeasures spec)

makeMeasureSpec' = mapFst (mapSnd uRType <$>) . Ms.dataConTypes . first (mapReft ur_reft)

makeClassMeasureSpec (Ms.MSpec {..}) = tx <$> M.elems cmeasMap
  where
    tx (M n s _) = (n, CM n (mapReft ur_reft s) -- [(t,m) | (IM n' t m) <- imeas, n == n']
                   )


mkMeasureDCon :: Ms.MSpec t LocSymbol -> BareM (Ms.MSpec t DataCon)
mkMeasureDCon m = (forM (measureCtors m) $ \n -> (val n,) <$> lookupGhcDataCon n)
                  >>= (return . mkMeasureDCon_ m)

mkMeasureDCon_ :: Ms.MSpec t LocSymbol -> [(Symbol, DataCon)] -> Ms.MSpec t DataCon
mkMeasureDCon_ m ndcs = m' {Ms.ctorMap = cm'}
  where 
    m'  = fmap (tx.val) m
    cm' = hashMapMapKeys (tx' . tx) $ Ms.ctorMap m'
    tx  = mlookup (M.fromList ndcs)
    tx' = dataConSymbol

measureCtors ::  Ms.MSpec t LocSymbol -> [LocSymbol]
measureCtors = sortNub . fmap ctor . concat . M.elems . Ms.ctorMap

-- mkMeasureSort :: (PVarable pv, Reftable r) => Ms.MSpec (BRType pv r) bndr-> BareM (Ms.MSpec (RRType pv r) bndr)
mkMeasureSort (Ms.MSpec c mm cm im)
  = Ms.MSpec c <$> forM mm tx <*> forM cm tx <*> forM im tx
    where
      tx m = liftM (\s' -> m {sort = s'}) (ofMeaSort (sort m))



varMeasures vars   = [ (symbol v, varSpecType v)  | v <- vars, isDataConWorkId v, isSimpleType $ varType v ]
varSpecType v      = Loc (getSourcePos v) (ofType $ varType v)
isSimpleType t     = null tvs && isNothing (splitFunTy_maybe tb) where (tvs, tb) = splitForAllTys t 



--------------------------------------------------------------------------------
-- Expand Measures -------------------------------------------------------------
--------------------------------------------------------------------------------

expandMeasure m
  = do eqns <- sequence $ expandMeasureDef <$> (eqns m)
       return $ m { sort = generalize (sort m)
                  , eqns = eqns }

expandMeasureDef :: Def LocSymbol -> BareM (Def LocSymbol)
expandMeasureDef d
  = do body <- expandMeasureBody (loc $ measure d) $ body d
       return $ d { body = body }

expandMeasureBody :: SourcePos -> Body -> BareM Body
expandMeasureBody l (P p)   = P   <$> (resolve l =<< expandPred p)
expandMeasureBody l (R x p) = R x <$> (resolve l =<< expandPred p)
expandMeasureBody l (E e)   = E   <$> resolve l e

