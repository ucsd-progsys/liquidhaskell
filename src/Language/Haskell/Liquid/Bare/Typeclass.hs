{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleContexts          #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Bare.Typeclass
  ( compileClasses
  , elaborateClassDcp
  , makeClassAuxTypes
  -- , makeClassSelectorSigs
  )
where

-- TODO: Handle typeclasses with a single method (newtype)

import           Control.Monad                  ( forM, guard )
import qualified Data.List                     as L
import qualified Data.HashSet                  as S
import           Data.Hashable                  ()
import qualified Data.Maybe                    as Mb
import qualified Language.Fixpoint.Types       as F
import qualified Language.Fixpoint.Misc        as Misc
import           Optics
import           Language.Haskell.Liquid.Bare.Elaborate
import qualified Liquid.GHC.Misc
                                               as GM
import qualified Liquid.GHC.API
                                               as Ghc
import qualified Language.Haskell.Liquid.Misc  as Misc
import           Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.RefType
                                               as RT
import qualified Language.Haskell.Liquid.Bare.Types
                                               as Bare
import qualified Language.Haskell.Liquid.Bare.Resolve
                                               as Bare
import qualified Language.Haskell.Liquid.Measure
                                               as Ms
-- import           Language.Haskell.Liquid.Types.Types
import qualified Data.HashMap.Strict           as M



compileClasses
  :: GhcSrc
  -> Bare.Env
  -> (ModName, Ms.BareSpec)
  -> [(ModName, Ms.BareSpec)]
  -> (Ms.BareSpec, [(Ghc.ClsInst, [Ghc.Var])])
compileClasses src env (name, spec) rest =
  (spec { sigs = sigsNew } <> clsSpec, instmethods)
 where
  clsSpec = mempty
    { dataDecls = clsDecls
    , reflects  = F.notracepp "reflects " $ S.fromList
                    (  fmap
                        ( fmap GM.dropModuleNames
                        . GM.namedLocSymbol
                        . Ghc.instanceDFunId
                        . fst
                        )
                        instClss
                    ++ methods
                    )
    }
  clsDecls                = makeClassDataDecl (M.toList refinedMethods)
      -- class methods
  (refinedMethods, sigsNew) = foldr grabClassSig (mempty, mempty) (sigs spec)
  grabClassSig
    :: (F.LocSymbol, ty)
    -> (M.HashMap Ghc.Class [(Ghc.Id, ty)], [(F.LocSymbol, ty)])
    -> (M.HashMap Ghc.Class [(Ghc.Id, ty)], [(F.LocSymbol, ty)])
  grabClassSig sigPair@(lsym, ref) (refs, sigs') = case clsOp of
    Nothing         -> (refs, sigPair : sigs')
    Just (cls, sig) -> (M.alter (merge sig) cls refs, sigs')
   where
    clsOp = do
      var <- Bare.maybeResolveSym env name "grabClassSig" lsym
      cls <- Ghc.isClassOpId_maybe var
      pure (cls, (var, ref))
    merge sig v = case v of
      Nothing -> Just [sig]
      Just vs -> Just (sig : vs)
  methods = [ GM.namedLocSymbol x | (_, xs) <- instmethods, x <- xs ]
      -- instance methods

  mkSymbol x
    | Ghc.isDictonaryId x = F.mappendSym "$" (F.dropSym 2 $ GM.simplesymbol x)
    | otherwise           = F.dropSym 2 $ GM.simplesymbol x

  instmethods :: [(Ghc.ClsInst, [Ghc.Var])]
  instmethods =
    [ (inst, ms)
    | (inst, cls) <- instClss
    , let selIds = GM.dropModuleNames . F.symbol <$> Ghc.classAllSelIds cls
    , (_, e) <- Mb.maybeToList
      (GM.findVarDefMethod
        (GM.dropModuleNames . F.symbol $ Ghc.instanceDFunId inst)
        (_giCbs src)
      )
    , let ms = filter (\x -> GM.isMethod x && elem (mkSymbol x) selIds)
                      (freeVars mempty e)
    ]
  instClss :: [(Ghc.ClsInst, Ghc.Class)]
  instClss =
    [ (inst, cls)
    | inst <- mconcat . Mb.maybeToList . _gsCls $ src
    , Ghc.moduleName (Ghc.nameModule (Ghc.getName inst)) == getModName name
    , let cls = Ghc.is_cls inst
    , cls `elem` refinedClasses
    ]
  refinedClasses :: [Ghc.Class]
  refinedClasses =
    Mb.mapMaybe resolveClassMaybe clsDecls
      ++ concatMap (Mb.mapMaybe resolveClassMaybe . dataDecls . snd) rest
  resolveClassMaybe :: DataDecl -> Maybe Ghc.Class
  resolveClassMaybe d =
    Bare.maybeResolveSym env
                         name
                         "resolveClassMaybe"
                         (dataNameSymbol . tycName $ d)
      >>= Ghc.tyConClass_maybe


-- a list of class with user defined refinements
makeClassDataDecl :: [(Ghc.Class, [(Ghc.Id, LocBareType)])] -> [DataDecl]
makeClassDataDecl = fmap (uncurry classDeclToDataDecl)

-- TODO: I should have the knowledge to construct DataConP manually than
-- following the rather unwieldy pipeline: Resolved -> Unresolved -> Resolved.
-- maybe this should be fixed right after the GHC API refactoring?
classDeclToDataDecl :: Ghc.Class -> [(Ghc.Id, LocBareType)] -> DataDecl
classDeclToDataDecl cls refinedIds = DataDecl
  { tycName   = DnName (F.symbol <$> GM.locNamedThing cls)
  , tycTyVars = tyVars
  , tycPVars  = []
  , tycDCons  = Just [dctor]
  , tycSrcPos = F.loc . GM.locNamedThing $ cls
  , tycSFun   = Nothing
  , tycPropTy = Nothing
  , tycKind   = DataUser
  }
 where
  dctor = F.notracepp "classDeclToDataDecl" DataCtor { dcName   = F.dummyLoc $ F.symbol classDc
    -- YL: same as class tyvars??
    -- Ans: it's been working so far so probably yes
                   , dcTyVars = tyVars
    -- YL: what is theta?
    -- Ans: where class constraints should go yet remain unused
    -- maybe should factor this out?
                   , dcTheta  = []
                   , dcFields = fields
                   , dcResult = Nothing
                   }

  tyVars = F.symbol <$> Ghc.classTyVars cls

  fields = fmap attachRef classIds
  attachRef sid
    | Just ref <- L.lookup sid refinedIds
    = (F.symbol sid, RT.subts tyVarSubst (F.val ref))
    | otherwise
    = (F.symbol sid, RT.bareOfType . dropTheta . Ghc.varType $ sid)

  tyVarSubst = [ (GM.dropModuleUnique v, v) | v <- tyVars ]

  -- FIXME: dropTheta should not be needed as long as we 
  -- handle classes and ordinary data types separately
  -- Might be helpful if we add an additional field for
  -- typeclasses
  dropTheta :: Ghc.Type -> Ghc.Type
  dropTheta = Misc.thd3 . Ghc.tcSplitMethodTy

  classIds  = Ghc.classAllSelIds cls
  classDc   = Ghc.classDataCon cls

-- | 'elaborateClassDcp' behaves differently from other datacon
--    functions. Each method type contains the full forall quantifiers
--    instead of having them chopped off
elaborateClassDcp
  :: (Ghc.CoreExpr -> F.Expr)
  -> (Ghc.CoreExpr -> Ghc.TcRn Ghc.CoreExpr)
  -> DataConP
  -> Ghc.TcRn (DataConP, DataConP)
elaborateClassDcp coreToLg simplifier dcp = do
  t' <- flip (zipWith addCoherenceOblig) prefts
    <$> forM fts (elaborateSpecType coreToLg simplifier)
  let ts' = elaborateMethod (F.symbol dc) (S.fromList xs) <$> t'
  pure
    ( dcp { dcpTyArgs = zip xs (stripPred <$> ts') }
    , dcp { dcpTyArgs = fmap (\(x, t) -> (x, strengthenTy x t)) (zip xs t') }
    )
 where
  addCoherenceOblig :: SpecType -> Maybe RReft -> SpecType
  addCoherenceOblig t Nothing  = t
  addCoherenceOblig t (Just r) = fromRTypeRep rrep
    { ty_res = res `RT.strengthen` r
    }
   where
    rrep = toRTypeRep t
    res  = ty_res rrep
  prefts =
    L.reverse
      .  take (length fts)
      $  fmap (Just . flip MkUReft mempty . mconcat) preftss
      ++ repeat Nothing
  preftss = (fmap . fmap) (uncurry (GM.coherenceObligToRef recsel))
                          (GM.buildCoherenceOblig cls)

  -- ugly, should have passed cls as an argument
  cls      = Mb.fromJust $ Ghc.tyConClass_maybe (Ghc.dataConTyCon dc)
  recsel   = F.symbol ("lq$recsel" :: String)
  resTy    = dcpTyRes dcp
  dc       = dcpCon dcp
  tvars    = (\x -> (makeRTVar x, mempty)) <$> dcpFreeTyVars dcp
      -- check if the names are qualified
  (xs, ts) = unzip (dcpTyArgs dcp)
  fts      = fullTy <$> ts
      -- turns forall a b. (a -> b) -> f a -> f b into
      -- forall f. Functor f => forall a b. (a -> b) -> f a -> f b
  stripPred :: SpecType -> SpecType
  stripPred = Misc.fourth4 . bkUnivClass
  fullTy :: SpecType -> SpecType
  fullTy t = mkArrow
    tvars
    []
    []
    [ ( recsel{- F.symbol dc-}
      , classRFInfo True
      , resTy
      , mempty
      )
    ]
    t
  -- YL: is this redundant if we already have strengthenClassSel?
  strengthenTy :: F.Symbol -> SpecType -> SpecType
  strengthenTy x t = mkUnivs tvs pvs (RFun z i clas (t' `RT.strengthen` mt) r)
   where
    (tvs, pvs, RFun z i clas t' r) = bkUniv t
    vv = rTypeValueVar t'
    mt = RT.uReft (vv, F.PAtom F.Eq (F.EVar vv) (F.EApp (F.EVar x) (F.EVar z)))


elaborateMethod :: F.Symbol -> S.HashSet F.Symbol -> SpecType -> SpecType
elaborateMethod dc methods st = mapExprReft
  (\_ -> substClassOpBinding tcbindSym dc methods)
  st
 where
  tcbindSym = grabtcbind st
  grabtcbind :: SpecType -> F.Symbol
  grabtcbind t =
    F.notracepp "grabtcbind"
      $ case Misc.fst4 . Misc.snd3 . bkArrow . Misc.thd3 . bkUniv $ t of
          tcbind : _ -> tcbind
          []         -> impossible
            Nothing
            (  "elaborateMethod: inserted dictionary binder disappeared:"
            ++ F.showpp t
            )


-- Before: Functor.fmap ($p1Applicative $dFunctor)
-- After: Funcctor.fmap ($p1Applicative##GHC.Base.Applicative)
substClassOpBinding
  :: F.Symbol -> F.Symbol -> S.HashSet F.Symbol -> F.Expr -> F.Expr
substClassOpBinding tcbind dc methods = go
 where
  go :: F.Expr -> F.Expr
  go (F.EApp e0 e1)
    | F.EVar x <- e0, F.EVar y <- e1, y == tcbind, S.member x methods = F.EVar
      (x `F.suffixSymbol` dc)
    | otherwise = F.EApp (go e0) (go e1)
  go (F.ENeg e          ) = F.ENeg (go e)
  go (F.EBin bop e0 e1  ) = F.EBin bop (go e0) (go e1)
  go (F.EIte e0  e1 e2  ) = F.EIte (go e0) (go e1) (go e2)
  go (F.ECst e0     s   ) = F.ECst (go e0) s
  go (F.ELam (x, t) body) = F.ELam (x, t) (go body)
  go (F.PAnd es         ) = F.PAnd (go <$> es)
  go (F.POr  es         ) = F.POr (go <$> es)
  go (F.PNot e          ) = F.PNot (go e)
  go (F.PImp e0 e1      ) = F.PImp (go e0) (go e1)
  go (F.PIff e0 e1      ) = F.PIff (go e0) (go e1)
  go (F.PAtom brel e0 e1) = F.PAtom brel (go e0) (go e1)
  -- a catch-all binding is not a good idea
  go e                    = e


renameTvs :: (F.Symbolic tv, F.PPrint tv) => (tv -> tv) -> RType c tv r -> RType c tv r
renameTvs rename t
  | RVar tv r <- t
  = RVar (rename tv) r
  | RFun b i tin tout r <- t
  = RFun b i (renameTvs rename tin) (renameTvs rename tout) r
  | RImpF b i tin tout r <- t
  = RImpF b i (renameTvs rename tin) (renameTvs rename tout) r
  | RAllT (RTVar tv info) tres r <- t
  = RAllT (RTVar (rename tv) info) (renameTvs rename tres) r
  | RAllP b tres <- t
  = RAllP (renameTvs rename <$> b) (renameTvs rename tres)
  | RApp tc ts tps r <- t
  -- TODO: handle rtprop properly
  = RApp tc (renameTvs rename <$> ts) tps r
  | RAllE b allarg ty <- t
  = RAllE b (renameTvs rename allarg) (renameTvs rename ty)
  | REx b exarg ty <- t
  = REx b   (renameTvs rename exarg) (renameTvs rename ty)
  | RExprArg _ <- t
  = t
  | RAppTy arg res r <- t
  = RAppTy (renameTvs rename arg) (renameTvs rename res) r
  | RRTy env r obl ty <- t
  = RRTy (over (each % _2) (renameTvs rename) env) r obl (renameTvs rename ty)
  | RHole _ <- t
  = t


makeClassAuxTypes ::
     (SpecType -> Ghc.TcRn SpecType)
  -> [F.Located DataConP]
  -> [(Ghc.ClsInst, [Ghc.Var])]
  -> Ghc.TcRn [(Ghc.Var, LocSpecType)]
makeClassAuxTypes elab dcps xs = Misc.concatMapM (makeClassAuxTypesOne elab) dcpInstMethods
  where
    dcpInstMethods = do
      dcp <- dcps
      (inst, methods) <- xs
      let dc = dcpCon . F.val $ dcp
              -- YL: only works for non-newtype class
          dc' = Ghc.classDataCon $ Ghc.is_cls inst
      guard $ dc == dc'
      pure (dcp, inst, methods)

makeClassAuxTypesOne ::
     (SpecType -> Ghc.TcRn SpecType)
  -> (F.Located DataConP, Ghc.ClsInst, [Ghc.Var])
  -> Ghc.TcRn [(Ghc.Var, LocSpecType)]
makeClassAuxTypesOne elab (ldcp, inst, methods) =
  forM methods $ \method -> do
    let (headlessSig, preft) =
          case L.lookup (mkSymbol method) yts' of
            Nothing ->
              impossible Nothing ("makeClassAuxTypesOne : unreachable?" ++ F.showpp (mkSymbol method) ++ " " ++ F.showpp yts)
            Just sig -> sig
        -- dict binder will never be changed because we optimized PAnd[]
        -- lq0 lq1 ...
            -- 
        ptys    = [(F.vv (Just i), classRFInfo True, pty, mempty) | (i,pty) <- zip [0,1..] isPredSpecTys]
        fullSig =
          mkArrow
            (zip isRTvs (repeat mempty))
            []
            []
            ptys .
          subst (zip clsTvs isSpecTys) $
          headlessSig
    elaboratedSig  <- flip addCoherenceOblig preft <$> elab fullSig

    let retSig =  mapExprReft (\_ -> substAuxMethod dfunSym methodsSet) (F.notracepp ("elaborated" ++ GM.showPpr method) elaboratedSig)
    let tysub  = F.notracepp "tysub" $ M.fromList $ zip (F.notracepp "newtype-vars" $ allTyVars' (F.notracepp "new-type" retSig)) (F.notracepp "ghc-type-vars" (allTyVars' ((F.notracepp "ghc-type" $ ofType (Ghc.varType method)) :: SpecType)))
        cosub  = M.fromList [ (F.symbol a, F.fObj (GM.namedLocSymbol b)) |  (a,RTV b) <- M.toList tysub]
        tysubf x = F.notracepp ("cosub:" ++ F.showpp cosub) $ tysub ^. at x % non x
        subbedTy = mapReft (Bare.coSubRReft cosub) (renameTvs tysubf retSig)
    -- need to make the variable names consistent
    pure (method, F.dummyLoc (F.notracepp ("vars:" ++ F.showpp (F.symbol <$> allTyVars' subbedTy)) subbedTy))

  -- "is" is used as a shorthand for instance, following the convention of the Ghc api
  where
    -- recsel = F.symbol ("lq$recsel" :: String)
    (_,predTys,_,_) = Ghc.instanceSig inst
    dfunApped = F.mkEApp dfunSymL [F.eVar $ F.vv (Just i) | (i,_) <- zip [0,1..] predTys]
    prefts  = L.reverse . take (length yts) $ fmap (F.notracepp "prefts" . Just . flip MkUReft mempty . mconcat) preftss ++ repeat Nothing
    preftss = F.notracepp "preftss" $ (fmap.fmap) (uncurry (GM.coherenceObligToRefE dfunApped)) (GM.buildCoherenceOblig cls)
    yts' = zip (fst <$> yts) (zip (snd <$> yts) prefts)
    cls = Mb.fromJust . Ghc.tyConClass_maybe $ Ghc.dataConTyCon (dcpCon dcp)
    addCoherenceOblig  :: SpecType -> Maybe RReft -> SpecType
    addCoherenceOblig t Nothing = t
    addCoherenceOblig t (Just r) = F.notracepp "SCSel" . fromRTypeRep $ rrep {ty_res = res `strengthen` r}
      where rrep = toRTypeRep t
            res  = ty_res rrep    -- (Monoid.mappend -> $cmappend##Int, ...)
    -- core rewriting mark2: do the same thing except they don't have to be symbols
    -- YL: poorly written. use a comprehension instead of assuming 
    methodsSet = F.notracepp "methodSet" $ M.fromList (zip (F.symbol <$> clsMethods) (F.symbol <$> methods))
    -- core rewriting mark1: dfunId
    -- ()
    dfunSymL = GM.namedLocSymbol $ Ghc.instanceDFunId inst
    dfunSym = F.val dfunSymL
    (isTvs, isPredTys, _, isTys) = Ghc.instanceSig inst
    isSpecTys = ofType <$> isTys
    isPredSpecTys = ofType <$> isPredTys
    isRTvs = makeRTVar . rTyVar <$> isTvs
    dcp = F.val ldcp
    -- Monoid.mappend, ...
    clsMethods = filter (\x -> GM.dropModuleNames (F.symbol x) `elem` fmap mkSymbol methods) $
      Ghc.classAllSelIds (Ghc.is_cls inst)
    yts = [(GM.dropModuleNames y, t) | (y, t) <- dcpTyArgs dcp]
    mkSymbol x
      | -- F.notracepp ("isDictonaryId:" ++ GM.showPpr x) $
        Ghc.isDictonaryId x = F.mappendSym "$" (F.dropSym 2 $ GM.simplesymbol x)
      | otherwise = F.dropSym 2 $ GM.simplesymbol x
        -- res = dcpTyRes dcp
    clsTvs = dcpFreeTyVars dcp
        -- copy/pasted from Bare/Class.hs
    subst [] t = t
    subst ((a, ta):su) t = subsTyVarMeet' (a, ta) (subst su t)

substAuxMethod :: F.Symbol -> M.HashMap F.Symbol F.Symbol -> F.Expr -> F.Expr
substAuxMethod dfun methods = F.notracepp "substAuxMethod" . go
  where go :: F.Expr -> F.Expr
        go (F.EApp e0 e1)
          | F.EVar x <- F.notracepp "e0" e0
          , (F.EVar dfun_mb, args)  <- F.splitEApp e1
          , dfun_mb == dfun
          , Just method <- M.lookup x methods
              -- Before: Functor.fmap ($p1Applicative $dFunctor)
              -- After: Funcctor.fmap ($p1Applicative##GHC.Base.Applicative)
           = F.eApps (F.EVar method) args
          | otherwise
          = F.EApp (go e0) (go e1)
        go (F.ENeg e) = F.ENeg (go e)
        go (F.EBin bop e0 e1) = F.EBin bop (go e0) (go e1)
        go (F.EIte e0 e1 e2) = F.EIte (go e0) (go e1) (go e2)
        go (F.ECst e0 s) = F.ECst (go e0) s
        go (F.ELam (x, t) body) = F.ELam (x, t) (go body)
        go (F.PAnd es) = F.PAnd (go <$> es)
        go (F.POr es) = F.POr (go <$> es)
        go (F.PNot e) = F.PNot (go e)
        go (F.PImp e0 e1) = F.PImp (go e0) (go e1)
        go (F.PIff e0 e1) = F.PIff (go e0) (go e1)
        go (F.PAtom brel e0 e1) = F.PAtom brel (go e0) (go e1)
        go e = F.notracepp "LEAF" e
