{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE TupleSections     #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Bare.Class
  ( makeClasses
  , makeCLaws
  , makeSpecDictionaries
  , makeDefaultMethods
  , makeMethodTypes
  )
  where

import           Data.Bifunctor
import qualified Data.Maybe                                 as Mb
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M

import qualified Language.Fixpoint.Misc                     as Misc
import qualified Language.Fixpoint.Types                    as F
import qualified Language.Fixpoint.Types.Visitor            as F

import           Language.Haskell.Liquid.Types.Dictionaries
import qualified Liquid.GHC.Misc           as GM
import qualified Liquid.GHC.API            as Ghc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types              hiding (freeTyVars)

import qualified Language.Haskell.Liquid.Measure            as Ms
import           Language.Haskell.Liquid.Bare.Types         as Bare
import           Language.Haskell.Liquid.Bare.Resolve       as Bare
import           Language.Haskell.Liquid.Bare.Expand        as Bare
import           Language.Haskell.Liquid.Bare.Misc         as Bare

import           Text.PrettyPrint.HughesPJ (text)
import qualified Control.Exception                 as Ex
import Control.Monad (forM)



-------------------------------------------------------------------------------
makeMethodTypes :: Bool -> DEnv Ghc.Var LocSpecType -> [DataConP] -> [Ghc.CoreBind] -> [(Ghc.Var, MethodType LocSpecType)]
-------------------------------------------------------------------------------
makeMethodTypes allowTC (DEnv hm) cls cbs
  = [(x, MT (addCC allowTC x . fromRISig <$> methodType d x hm) (addCC allowTC x <$> classType (splitDictionary e) x)) | (d,e) <- ds, x <- grepMethods e]
    where
      grepMethods = filter GM.isMethod . freeVars mempty
      ds = filter (GM.isDictionary . fst) (concatMap unRec cbs)
      unRec (Ghc.Rec xes) = xes
      unRec (Ghc.NonRec x e) = [(x,e)]

      classType Nothing _ = Nothing
      classType (Just (d, ts, _)) x =
        case filter ((==d) . Ghc.dataConWorkId . dcpCon) cls of
          (di:_) -> (dcpLoc di `F.atLoc`) . subst (zip (dcpFreeTyVars di) ts) <$> L.lookup (mkSymbol x) (dcpTyArgs di)
          _      -> Nothing

      methodType d x m = ihastype (M.lookup d m) x

      ihastype Nothing _    = Nothing
      ihastype (Just xts) x = M.lookup (mkSymbol x) xts

      mkSymbol x = F.dropSym 2 $ GM.simplesymbol x

      subst [] t = t
      subst ((a,ta):su) t = subsTyVarMeet' (a,ofType ta) (subst su t)

addCC :: Bool -> Ghc.Var -> LocSpecType -> LocSpecType
addCC allowTC var zz@(Loc l l' st0)
  = Loc l l'
  . addForall hst
  . mkArrow [] ps' [] []
  . makeCls cs'
  . mapExprReft (\_ -> F.applyCoSub coSub)
  . subts su
  $ st
  where
    hst           = ofType (Ghc.expandTypeSynonyms t0) :: SpecType
    t0            = Ghc.varType var
    tyvsmap       = case Bare.runMapTyVars allowTC t0 st err of
                          Left e  -> Ex.throw e
                          Right s -> Bare.vmap s
    su            = [(y, rTyVar x)           | (x, y) <- tyvsmap]
    su'           = [(y, RVar (rTyVar x) ()) | (x, y) <- tyvsmap] :: [(RTyVar, RSort)]
    coSub         = M.fromList [(F.symbol y, F.FObj (F.symbol x)) | (y, x) <- su]
    ps'           = fmap (subts su') <$> ps
    cs'           = [(F.dummySymbol, RApp c ts [] mempty) | (c, ts) <- cs ]
    (_,_,cs,_)    = bkUnivClass (F.notracepp "hs-spec" $ ofType (Ghc.expandTypeSynonyms t0) :: SpecType)
    (_,ps,_ ,st)  = bkUnivClass (F.notracepp "lq-spec" st0)

    makeCls c t  = foldr (uncurry rFun) t c
    err hsT lqT   = ErrMismatch (GM.fSrcSpan zz) (pprint var)
      (text "makeMethodTypes")
      (pprint $ Ghc.expandTypeSynonyms t0)
      (pprint $ toRSort st0)
      (Just (hsT, lqT))
      (Ghc.getSrcSpan var)

    addForall (RAllT v t r) tt@(RAllT v' _ _)
      | v == v'
      = tt
      | otherwise
      = RAllT (updateRTVar v) (addForall t tt) r
    addForall (RAllT v t r) t'
      = RAllT (updateRTVar v) (addForall t t') r
    addForall (RAllP _ t) t'
      = addForall t t'
    addForall _ (RAllP p t')
      = RAllP (fmap (subts su') p) t'
    addForall (RFun _ _ t1 t2 _) (RFun x i t1' t2' r)
      = RFun x i (addForall t1 t1') (addForall t2 t2') r
    addForall _ t
      = t


splitDictionary :: Ghc.CoreExpr -> Maybe (Ghc.Var, [Ghc.Type], [Ghc.Var])
splitDictionary = go [] []
  where
    go ts xs (Ghc.App e (Ghc.Tick _ a)) = go ts xs (Ghc.App e a)
    go ts xs (Ghc.App e (Ghc.Type t))   = go (t:ts) xs e
    go ts xs (Ghc.App e (Ghc.Var x))    = go ts (x:xs) e
    go ts xs (Ghc.Tick _ t) = go ts xs t
    go ts xs (Ghc.Var x) = Just (x, reverse ts, reverse xs)
    go _ _ _ = Nothing


-------------------------------------------------------------------------------
makeCLaws :: Bare.Env -> Bare.SigEnv -> ModName -> Bare.ModSpecs
          -> Bare.Lookup [(Ghc.Class, [(ModName, Ghc.Var, LocSpecType)])]
-------------------------------------------------------------------------------
makeCLaws env sigEnv myName specs = do
  zMbs <- forM classTcs $ \(name, clss, tc) -> do
            clsMb <- mkClass env sigEnv myName name clss tc
            case clsMb of
              Nothing ->
                return Nothing
              Just cls -> do
                gcls <- Mb.maybe (err tc) Right (Ghc.tyConClass_maybe tc)
                return $ Just (gcls, snd cls)
  return (Mb.catMaybes zMbs)
  where
    err tc   = error ("Not a type class: " ++ F.showpp tc)
    classTc  = Bare.maybeResolveSym env myName "makeClass" . btc_tc . rcName
    classTcs = [ (name, cls, tc) | (name, spec) <- M.toList specs
                                 , cls          <- Ms.claws spec
                                 , tc           <- Mb.maybeToList (classTc cls)
               ]

-------------------------------------------------------------------------------
makeClasses :: Bare.Env -> Bare.SigEnv -> ModName -> Bare.ModSpecs
            -> Bare.Lookup ([DataConP], [(ModName, Ghc.Var, LocSpecType)])
-------------------------------------------------------------------------------
makeClasses env sigEnv myName specs = do
  mbZs <- forM classTcs $ \(name, cls, tc) ->
            mkClass env sigEnv myName name cls tc
  return . second mconcat . unzip . Mb.catMaybes $ mbZs
  where
    classTcs = [ (name, cls, tc) | (name, spec) <- M.toList specs
                                 , cls          <- Ms.classes spec
                                 , tc           <- Mb.maybeToList (classTc cls) ]
    classTc = Bare.maybeResolveSym env myName "makeClass" . btc_tc . rcName

mkClass :: Bare.Env -> Bare.SigEnv -> ModName -> ModName -> RClass LocBareType -> Ghc.TyCon
        -> Bare.Lookup (Maybe (DataConP, [(ModName, Ghc.Var, LocSpecType)]))
mkClass env sigEnv _myName name (RClass cc ss as ms)
  = Bare.failMaybe env name
  . mkClassE env sigEnv _myName name (RClass cc ss as ms)

mkClassE :: Bare.Env -> Bare.SigEnv -> ModName -> ModName -> RClass LocBareType -> Ghc.TyCon
         -> Bare.Lookup (DataConP, [(ModName, Ghc.Var, LocSpecType)])
mkClassE env sigEnv _myName name (RClass cc ss as ms) tc = do
    ss'    <- mapM (mkConstr   env sigEnv name) ss
    meths  <- mapM (makeMethod env sigEnv name) ms'
    let vts = [ (m, v, t) | (m, kv, t) <- meths, v <- Mb.maybeToList (plugSrc kv) ]
    let sts = [(val s, unClass $ val t) | (s, _) <- ms | (_, _, t) <- meths]
    let dcp = DataConP l dc αs [] (val <$> ss') (reverse sts) rt False (F.symbol name) l'
    return  $ F.notracepp msg (dcp, vts)
  where
    c      = btc_tc cc
    l      = loc  c
    l'     = locE c
    msg    = "MKCLASS: " ++ F.showpp (cc, as, αs)
    (dc:_) = Ghc.tyConDataCons tc
    αs     = bareRTyVar <$> as
    as'    = [rVar $ GM.symbolTyVar $ F.symbol a | a <- as ]
    ms'    = [ (s, rFun "" (RApp cc (flip RVar mempty <$> as) [] mempty) <$> t) | (s, t) <- ms]
    rt     = rCls tc as'

mkConstr :: Bare.Env -> Bare.SigEnv -> ModName -> LocBareType -> Bare.Lookup LocSpecType
mkConstr env sigEnv name = fmap (fmap dropUniv) . Bare.cookSpecTypeE env sigEnv name Bare.GenTV
  where
    dropUniv t           = t' where (_, _, t') = bkUniv t

   --FIXME: cleanup this code
unClass :: SpecType -> SpecType
unClass = snd . bkClass . thrd3 . bkUniv

makeMethod :: Bare.Env -> Bare.SigEnv -> ModName -> (LocSymbol, LocBareType)
           -> Bare.Lookup (ModName, PlugTV Ghc.Var, LocSpecType)
makeMethod env sigEnv name (lx, bt) = (name, mbV,) <$> Bare.cookSpecTypeE env sigEnv name mbV bt
  where
    mbV = maybe Bare.GenTV Bare.LqTV (Bare.maybeResolveSym env name "makeMethod" lx)

-------------------------------------------------------------------------------
makeSpecDictionaries :: Bare.Env -> Bare.SigEnv -> ModSpecs -> DEnv Ghc.Var LocSpecType
-------------------------------------------------------------------------------
makeSpecDictionaries env sigEnv specs
  = dfromList
  . concatMap (makeSpecDictionary env sigEnv)
  $ M.toList specs

makeSpecDictionary :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec)
                   -> [(Ghc.Var, M.HashMap F.Symbol (RISig LocSpecType))]
makeSpecDictionary env sigEnv (name, spec)
  = Mb.catMaybes
  . resolveDictionaries env name
  . fmap (makeSpecDictionaryOne env sigEnv name)
  . Ms.rinstance
  $ spec

makeSpecDictionaryOne :: Bare.Env -> Bare.SigEnv -> ModName
                      -> RInstance LocBareType
                      -> (F.Symbol, M.HashMap F.Symbol (RISig LocSpecType))
makeSpecDictionaryOne env sigEnv name (RI bt lbt xts)
         = makeDictionary $ F.notracepp "RI" $ RI bt ts [(x, mkLSpecIType t) | (x, t) <- xts ]
  where
    ts      = mkTy' <$> lbt
    rts     = concatMap (univs . val) ts
    univs t = (\(RTVar tv _, _) -> tv) <$> as where (as, _, _) = bkUniv t

    mkTy' :: LocBareType -> LocSpecType
    mkTy' = Bare.cookSpecType env sigEnv name Bare.GenTV
    mkTy :: LocBareType -> LocSpecType
    mkTy = fmap (mapUnis tidy) . Bare.cookSpecType env sigEnv name
               Bare.GenTV -- (Bare.HsTV (Bare.lookupGhcVar env name "rawDictionaries" x))
    mapUnis f t = mkUnivs (f as) ps t0 where (as, ps, t0) = bkUniv t

    tidy vs = l ++ r
      where (l,r) = L.partition (\(RTVar tv _,_) -> tv `elem` rts) vs

    mkLSpecIType :: RISig LocBareType -> RISig LocSpecType
    mkLSpecIType t = fmap mkTy t

resolveDictionaries :: Bare.Env -> ModName -> [(F.Symbol, M.HashMap F.Symbol (RISig LocSpecType))]
                    -> [Maybe (Ghc.Var, M.HashMap F.Symbol (RISig LocSpecType))]
resolveDictionaries env name = fmap lookupVar
                             . concatMap addInstIndex
                             . Misc.groupList
  where
    lookupVar (x, inst)      = (, inst) <$> Bare.maybeResolveSym env name "resolveDict" (F.dummyLoc x)

-- formerly, addIndex
-- GHC internal postfixed same name dictionaries with ints
addInstIndex            :: (F.Symbol, [a]) -> [(F.Symbol, a)]
addInstIndex (x, ks) = go (0::Int) (reverse ks)
  where
    go _ []          = []
    go _ [i]         = [(x, i)]
    go j (i:is)      = (F.symbol (F.symbolString x ++ show j),i) : go (j+1) is

----------------------------------------------------------------------------------
makeDefaultMethods :: Bare.Env -> [(ModName, Ghc.Var, LocSpecType)]
                   -> [(ModName, Ghc.Var, LocSpecType)]
----------------------------------------------------------------------------------
makeDefaultMethods env mts = [ (mname, dm, t)
                                 | (mname, m, t) <- mts
                                 , dm            <- lookupDefaultVar env mname m ]

lookupDefaultVar :: Bare.Env -> ModName -> Ghc.Var -> [Ghc.Var]
lookupDefaultVar env name v = Mb.maybeToList
                            . Bare.maybeResolveSym env name "default-method"
                            $ dmSym
  where
    dmSym                   = F.atLoc v (GM.qualifySymbol mSym dnSym)
    dnSym                   = F.mappendSym "$dm" nSym
    (mSym, nSym)            = GM.splitModuleName (F.symbol v)
