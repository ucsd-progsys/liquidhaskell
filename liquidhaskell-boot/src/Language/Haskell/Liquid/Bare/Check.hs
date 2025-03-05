{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module Language.Haskell.Liquid.Bare.Check
  ( checkTargetSpec
  , checkBareSpec
  , checkTargetSrc
  , tyCompat
  ) where


import           Language.Haskell.Liquid.Constraint.ToFixpoint

import           Liquid.GHC.API                   as Ghc hiding ( Located
                                                                                 , text
                                                                                 , (<+>)
                                                                                 , panic
                                                                                 , ($+$)
                                                                                 , empty
                                                                                 )
import           Control.Applicative                       ((<|>))
import           Control.Monad.Reader
import           Data.Maybe
import           Data.Function                             (on)
import           Text.PrettyPrint.HughesPJ                 hiding ((<>))
import qualified Data.List                                 as L
import qualified Data.HashMap.Strict                       as M
import qualified Data.HashSet                              as S
import           Data.Hashable
import qualified Language.Fixpoint.Misc                    as Misc
import           Language.Fixpoint.SortCheck               (ElabM, checkSorted, checkSortedReftFull, checkSortFull)
import qualified Language.Fixpoint.Types                   as F
import qualified Language.Haskell.Liquid.GHC.Misc          as GM
import           Language.Haskell.Liquid.GHC.Play          (getNonPositivesTyCon)
import           Language.Haskell.Liquid.Misc              (condNull, thd5, foldMapM)
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Visitors
import           Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure           as Ms
import qualified Language.Haskell.Liquid.Bare.Types        as Bare
import qualified Language.Haskell.Liquid.Bare.Resolve      as Bare
import           Language.Haskell.Liquid.UX.Config
import Language.Fixpoint.Types.Config (ElabFlags (ElabFlags), solverFlags)


----------------------------------------------------------------------------------------------
-- | Checking TargetSrc ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------
checkTargetSrc :: Config -> TargetSrc -> Either Diagnostics ()
checkTargetSrc cfg spec
  |  nopositivity cfg
  || nopositives == emptyDiagnostics
  = Right ()
  | otherwise
  = Left nopositives
  where nopositives = checkPositives (gsTcs spec)


checkPositives :: [TyCon] -> Diagnostics
checkPositives tys = mkDiagnostics [] $ mkNonPosError (getNonPositivesTyCon tys)

mkNonPosError :: [(TyCon, [DataCon])]  -> [Error]
mkNonPosError tcs = [ ErrPosTyCon (getSrcSpan tc) (pprint tc) (pprint dc <+> ":" <+> pprint (dataConRepType dc))
                    | (tc, dc:_) <- tcs]

----------------------------------------------------------------------------------------------
-- | Checking BareSpec ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------
checkBareSpec :: Ms.BareSpec -> Either Diagnostics ()
checkBareSpec sp
  | allChecks == emptyDiagnostics = Right ()
  | otherwise = Left allChecks
  where
    allChecks = mconcat [ checkUnique   "measure"    measures
                        , checkUnique   "field"      fields
                        , checkDisjoints             [ inlines
                                                     , hmeasures
                                                     , S.fromList measures
                                                     , reflects
                                                     , S.fromList fields
                                                     ]
                        ]
    inlines   = S.map (fmap getLHNameSymbol) (Ms.inlines sp)
    hmeasures = S.map (fmap getLHNameSymbol) (Ms.hmeas sp)
    reflects  = S.map (fmap getLHNameSymbol) (Ms.reflects sp)
    measures  = fmap getLHNameSymbol . msName <$> Ms.measures sp
    fields    = map (fmap getLHNameSymbol) $ concatMap dataDeclFields (Ms.dataDecls sp)

dataDeclFields :: DataDecl -> [F.Located LHName]
dataDeclFields = filter (not . GM.isTmpSymbol . getLHNameSymbol . F.val)
               . Misc.hashNubWith val
               . concatMap dataCtorFields
               . fromMaybe []
               . tycDCons

dataCtorFields :: DataCtor -> [F.Located LHName]
dataCtorFields c
  | isGadt c  = []
  | otherwise = F.atLoc c <$> [ f | (f,_) <- dcFields c ]

isGadt :: DataCtor -> Bool
isGadt = isJust . dcResult

checkUnique :: String -> [F.LocSymbol] -> Diagnostics
checkUnique _ = mkDiagnostics mempty . checkUnique' F.val GM.fSrcSpan

checkUnique' :: (PPrint a, Eq a, Hashable a)
             => (t -> a) -> (t -> Ghc.SrcSpan) -> [t] -> [Error]
checkUnique' nameF locF ts = [ErrDupSpecs l (pprint n) ls | (n, ls@(l:_)) <- dups]
  where
    dups                   = [ z      | z@(_, _:_:_) <- Misc.groupList nts       ]
    nts                    = [ (n, l) | t <- ts, let n = nameF t, let l = locF t ]

checkDisjoints :: [S.HashSet F.LocSymbol] -> Diagnostics
checkDisjoints []     = emptyDiagnostics
checkDisjoints [_]    = emptyDiagnostics
checkDisjoints (s:ss) = checkDisjoint s (S.unions ss) <> checkDisjoints ss

checkDisjoint :: S.HashSet F.LocSymbol -> S.HashSet F.LocSymbol -> Diagnostics
checkDisjoint s1 s2 = checkUnique "disjoint" (S.toList s1 ++ S.toList s2)

----------------------------------------------------------------------------------------------
-- | Checking TargetSpec
----------------------------------------------------------------------------------------------

checkTargetSpec :: [Ms.BareSpec]
                -> TargetSrc
                -> F.SEnv F.SortedReft
                -> [CoreBind]
                -> TargetSpec
                -> Either Diagnostics ()
checkTargetSpec specs src env cbs tsp
  | diagnostics == emptyDiagnostics = Right ()
  | otherwise                       = Left diagnostics
  where
    diagnostics      :: Diagnostics
    diagnostics      =  runReader (foldMapM (checkBind allowHO bsc "measure"      emb tcEnv env) (gsMeas       (gsData tsp))) ef
                     <> condNull noPrune
                        (runReader (foldMapM (checkBind allowHO bsc "constructor"  emb tcEnv env) (txCtors $ gsCtors      (gsData tsp))) ef)
                     <> runReader (foldMapM (checkBind allowHO bsc "assume"       emb tcEnv env) (gsAsmSigs    (gsSig tsp))) ef
                     <> runReader (foldMapM (checkBind allowHO bsc "reflect"      emb tcEnv env . (\sig@(_,s) -> F.notracepp (show (ty_info (toRTypeRep (F.val s)))) sig)) (gsRefSigs (gsSig tsp))) ef
                     <> runReader (checkTySigs allowHO bsc cbs            emb tcEnv env                (gsSig tsp)) ef
                     -- ++ mapMaybe (checkTerminationExpr             emb       env) (gsTexprs     (gsSig  sp))
                     <> runReader (foldMapM (checkBind allowHO bsc "class method" emb tcEnv env) (clsSigs      (gsSig tsp))) ef
                     <> runReader (foldMapM (checkInv allowHO bsc emb tcEnv env)                 (gsInvariants (gsData tsp))) ef
                     <> runReader (checkIAl allowHO bsc emb tcEnv env                            (gsIaliases   (gsData tsp))) ef
                     <> runReader (checkMeasures emb env ms) ef
                     <> checkClassMeasures                                        ms
                     <> checkClassMethods (gsCls src) (gsCMethods (gsVars tsp)) (gsTySigs     (gsSig tsp))
                     -- <> foldMap checkMismatch sigs
                     <> foldMap checkMismatch (L.filter (\(v,_) -> not (GM.isSCSel v || GM.isMethod v)) sigs)
                     <> checkDuplicate                                            (gsTySigs     (gsSig tsp))
                     -- TODO-REBARE ++ checkQualifiers env                                       (gsQualifiers (gsQual sp))
                     <> checkDuplicate                                            (gsAsmSigs    (gsSig tsp))
                     <> checkDupIntersect                                         (gsTySigs (gsSig tsp)) (gsAsmSigs (gsSig tsp))
                     <> checkRTAliases "Type Alias" env            tAliases
                     <> checkRTAliases "Pred Alias" env            eAliases
                     -- ++ _checkDuplicateFieldNames                   (gsDconsP sp)
                     -- NV TODO: allow instances of refined classes to be refined
                     -- but make sure that all the specs are checked.
                     -- ++ checkRefinedClasses                        rClasses rInsts
                     <> runReader (checkSizeFun emb env                                      (gsTconsP (gsName tsp))) ef
                     <> checkPlugged (catMaybes [ fmap (F.dropSym 2 $ GM.simplesymbol x,) (getMethodType t) | (x, t) <- gsMethods (gsSig tsp) ])
                     <> checkRewrites tsp
                     <> if allowUnsafeConstructors $ getConfig tsp
                          then mempty
                          else checkConstructorRefinement (gsTySigs $ gsSig tsp)

    _rClasses         = concatMap Ms.classes specs
    _rInsts           = concatMap Ms.rinstance specs
    tAliases          = concat [Ms.aliases sp  | sp <- specs]
    eAliases          = concat [Ms.ealiases sp | sp <- specs]
    emb              = gsTcEmbeds (gsName tsp)
    tcEnv            = gsTyconEnv (gsName tsp)
    ms               = gsMeasures (gsData tsp)
    clsSigs sp       = [ (v, t) | (v, t) <- gsTySigs sp, isJust (isClassOpId_maybe v) ]
    sigs             = gsTySigs (gsSig tsp) ++ gsAsmSigs (gsSig tsp) ++ gsCtors (gsData tsp)
    -- allowTC          = typeclass (getConfig sp)
    allowHO          = higherOrderFlag tsp
    bsc              = bscope (getConfig tsp)
    noPrune          = not (pruneFlag tsp)
    txCtors ts       = [(v, fmap (fmap (fmap (F.filterUnMatched temps))) t) | (v, t) <- ts]
    temps            = F.makeTemplates $ gsUnsorted $ gsData tsp
    ef               = maybe (ElabFlags False) solverFlags $ smtsolver $ getConfig tsp
    -- env'             = L.foldl' (\e (x, s) -> insertSEnv x (RR s mempty) e) env wiredSortedSyms



-- | Tests that the returned refinement type of data constructors has predicate @True@ or @prop v == e@.
--
-- > data T = T Int
-- > {-@ T :: x:Int -> { v:T | v = T x } @-} -- Should be rejected
-- > {-@ T :: x:Int -> { v:T | True } @-} -- Should be fine
-- > {-@ T :: x:Int -> { v:T | prop v = True } @-} -- Should be fine
--
checkConstructorRefinement :: [(Var, LocSpecType)] -> Diagnostics
checkConstructorRefinement = mconcat . map checkOne
  where
    checkOne (s, ty) | isCtorName s
                     , not $ validRef $ getRetTyRef $ val ty
                     = mkDiagnostics mempty [ ErrCtorRefinement (GM.sourcePosSrcSpan $ loc ty) (pprint s) ]
    checkOne _       = mempty

    getRetTyRef (RFun _ _ _ t _) = getRetTyRef t
    getRetTyRef (RAllT _ t _)    = getRetTyRef t
    getRetTyRef t                = ur_reft $ rt_reft t

    -- True refinement
    validRef (F.Reft (_, F.PTrue))
                      = True
    -- Prop foo from ProofCombinators
    validRef (F.Reft (v, F.PAtom F.Eq (F.EApp (F.EVar n) (F.EVar v')) _))
      | n == "Language.Haskell.Liquid.ProofCombinators.prop"
      , v == v'
      = True
    validRef _ = False

    isCtorName x = case idDetails x of
      DataConWorkId _ -> True
      DataConWrapId _ -> True
      _               -> False


checkPlugged :: PPrint v => [(v, LocSpecType)] -> Diagnostics
checkPlugged xs = mkDiagnostics mempty (map mkError (filter (hasHoleTy . val . snd) xs))
  where
    mkError (x,t) = ErrBadData (GM.sourcePosSrcSpan $ loc t) (pprint x) msg
    msg           = "Cannot resolve type hole `_`. Use explicit type instead."


--------------------------------------------------------------------------------
checkTySigs :: Bool
            -> BScope
            -> [CoreBind]
            -> F.TCEmb TyCon
            -> Bare.TyConMap
            -> F.SEnv F.SortedReft
            -> GhcSpecSig
            -> ElabM Diagnostics
--------------------------------------------------------------------------------
checkTySigs allowHO bsc cbs emb tcEnv senv sig =
  do ef <- ask
     pure $ mconcat (runReader (traverse (check senv) topTs) ef)
                   -- = concatMap (check env) topTs
                   -- (mapMaybe   (checkT env) [ (x, t)     | (x, (t, _)) <- topTs])
                   -- ++ (mapMaybe   (checkE env) [ (x, t, es) | (x, (t, Just es)) <- topTs])
                     <> coreVisitor (checkVisitor ef) senv emptyDiagnostics cbs
                   -- ++ coreVisitor checkVisitor env [] cbs
  where
    check :: F.SEnv F.SortedReft -> (Var, (LocSpecType, Maybe [Located F.Expr])) -> ElabM Diagnostics
    check          = checkSigTExpr allowHO bsc emb tcEnv
    locTm          = M.fromList locTs
    (locTs, topTs) = Bare.partitionLocalBinds vtes
    vtes           = [ (x, (t, es)) | (x, t) <- gsTySigs sig, let es = M.lookup x vExprs]
    vExprs         = M.fromList  [ (x, es) | (x, _, es) <- gsTexprs sig ]

    checkVisitor  :: ElabFlags -> CoreVisitor (F.SEnv F.SortedReft) Diagnostics
    checkVisitor ef = CoreVisitor
                       { envF  = \env v     -> F.insertSEnv (F.symbol v) (vSort v) env
                       , bindF = \env acc v -> runReader (errs env v) ef <> acc
                       , exprF = \_   acc _ -> acc
                       }
    vSort            = Bare.varSortedReft emb
    errs :: F.SEnv F.SortedReft -> Var -> ElabM Diagnostics
    errs env v       = case M.lookup v locTm of
                         Nothing -> pure emptyDiagnostics
                         Just t  -> check env (v, t)

checkSigTExpr :: Bool -> BScope -> F.TCEmb TyCon -> Bare.TyConMap -> F.SEnv F.SortedReft
              -> (Var, (LocSpecType, Maybe [Located F.Expr]))
              -> ElabM Diagnostics
checkSigTExpr allowHO bsc emb tcEnv env (x, (t, es)) =
  do ef <- ask
     pure $ runReader mbErr1 ef <> runReader mbErr2 ef
   where
    mbErr1 = checkBind allowHO bsc empty emb tcEnv env (x, t)
    mbErr2 = maybe (pure emptyDiagnostics) (checkTerminationExpr emb env . (x, t,)) es
    -- mbErr2 = checkTerminationExpr emb env . (x, t,) =<< es

-- | Used for termination checking. If we have no \"len\" defined /yet/ (for example we are checking
-- 'GHC.Prim') then we want to skip this check.
checkSizeFun :: F.TCEmb TyCon -> F.SEnv F.SortedReft -> [TyConP] -> ElabM Diagnostics
checkSizeFun emb env tys =
  do ef <- ask
     pure $ mkDiagnostics mempty (map mkError (mapMaybe (go ef) tys))
  where
    mkError ((f, tcp), msg)  = ErrTyCon (GM.sourcePosSrcSpan $ tcpLoc tcp)
                                 (text "Size function" <+> pprint (f x)
                                                       <+> text "should have type int, but it was "
                                                       <+> pprint (tcpCon tcp)
                                                       <+> text "."
                                                       $+$   msg)
                                 (pprint (tcpCon tcp))

    go :: ElabFlags -> TyConP -> Maybe ((F.Symbol -> F.Expr, TyConP), Doc)
    go ef tcp = case tcpSizeFun tcp of
               Nothing                   -> Nothing
               Just f | isWiredInLenFn f -> Nothing -- Skip the check.
               Just f                    -> checkWFSize ef (szFun f) tcp

    checkWFSize ef f tcp = ((f, tcp),) <$> runReader (checkSortFull (F.srcSpan tcp) (F.insertSEnv x (mkTySort (tcpCon tcp)) env) F.intSort (f x)) ef
    x                 = "x" :: F.Symbol
    mkTySort tc       = rTypeSortedReft emb (ofType $ TyConApp tc (TyVarTy <$> tyConTyVars tc) :: RRType ())

    isWiredInLenFn :: SizeFun -> Bool
    isWiredInLenFn IdSizeFun           = False
    isWiredInLenFn (SymSizeFun locSym) = isWiredIn locSym

checkInv :: Bool
         -> BScope
         -> F.TCEmb TyCon
         -> Bare.TyConMap
         -> F.SEnv F.SortedReft
         -> (Maybe Var, LocSpecType)
         -> ElabM Diagnostics
checkInv allowHO bsc emb tcEnv env (_, t) = checkTy allowHO bsc err emb tcEnv env t
  where
    err              = ErrInvt (GM.sourcePosSrcSpan $ loc t) (val t)

checkIAl :: Bool
         -> BScope
         -> F.TCEmb TyCon
         -> Bare.TyConMap
         -> F.SEnv F.SortedReft
         -> [(LocSpecType, LocSpecType)]
         -> ElabM Diagnostics
checkIAl allowHO bsc emb tcEnv env ss =
  do ds <- traverse (checkIAlOne allowHO bsc emb tcEnv env) ss
     pure $ mconcat ds

checkIAlOne :: Bool
            -> BScope
            -> F.TCEmb TyCon
            -> Bare.TyConMap
            -> F.SEnv F.SortedReft
            -> (LocSpecType, LocSpecType)
            -> ElabM Diagnostics
checkIAlOne allowHO bsc emb tcEnv env (t1, t2) =
  do cs <- traverse (\t -> checkTy allowHO bsc (err t) emb tcEnv env t) [t1, t2]
     pure $ mconcat $ checkEq : cs
  where
    err    t = ErrIAl (GM.sourcePosSrcSpan $ loc t) (val t)
    t1'      :: RSort
    t1'      = toRSort $ val t1
    t2'      :: RSort
    t2'      = toRSort $ val t2
    checkEq  = if t1' == t2' then emptyDiagnostics else mkDiagnostics mempty [errmis]
    errmis   = ErrIAlMis (GM.sourcePosSrcSpan $ loc t1) (val t1) (val t2) emsg
    emsg     = pprint t1 <+> text "does not match with" <+> pprint t2


-- FIXME: Should _ be removed if it isn't used?
checkRTAliases :: String -> t -> [Located (RTAlias s a)] -> Diagnostics
checkRTAliases msg _ as = err1s
  where
    err1s               = checkDuplicateRTAlias msg as

checkBind :: (PPrint v)
          => Bool
          -> BScope
          -> Doc
          -> F.TCEmb TyCon
          -> Bare.TyConMap
          -> F.SEnv F.SortedReft
          -> (v, LocSpecType)
          -> ElabM Diagnostics
checkBind allowHO bsc s emb tcEnv env (v, t) = checkTy allowHO bsc msg emb tcEnv env t
  where
    msg                      = ErrTySpec (GM.fSrcSpan t) (Just s) (pprint v) (val t)


checkTerminationExpr :: (Eq v, PPrint v)
                     => F.TCEmb TyCon
                     -> F.SEnv F.SortedReft
                     -> (v, LocSpecType, [F.Located F.Expr])
                     -> ElabM Diagnostics
checkTerminationExpr emb env (v, Loc l _ st, les) =
  do ef <- ask
     pure $ mkError "ill-sorted" (go ef les) <> mkError "non-numeric" (go' ef les)
  where
    -- es      = val <$> les
    mkError :: Doc -> Maybe (F.Expr, Doc) -> Diagnostics
    mkError _ Nothing = emptyDiagnostics
    mkError k (Just expr') =
      mkDiagnostics mempty [(\ (e, d) -> ErrTermSpec (GM.sourcePosSrcSpan l) (pprint v) k e st d) expr']
    -- mkErr   = uncurry (\ e d -> ErrTermSpec (GM.sourcePosSrcSpan l) (pprint v) (text "ill-sorted" ) e t d)
    -- mkErr'  = uncurry (\ e d -> ErrTermSpec (GM.sourcePosSrcSpan l) (pprint v) (text "non-numeric") e t d)

    go :: ElabFlags -> [F.Located F.Expr] -> Maybe (F.Expr, Doc)
    go ef     = L.foldl' (\err e -> err <|> (val e,) <$> runReader (checkSorted (F.srcSpan e) env' (val e)) ef)     Nothing

    go' :: ElabFlags -> [F.Located F.Expr] -> Maybe (F.Expr, Doc)
    go' ef    = L.foldl' (\err e -> err <|> (val e,) <$> runReader (checkSorted (F.srcSpan e) env' (cmpZero e)) ef) Nothing

    env'    = F.sr_sort <$> L.foldl' (\e (x,s) -> F.insertSEnv x s e) env xts
    xts     = concatMap mkClss $ zip (ty_binds trep) (ty_args trep)
    trep    = toRTypeRep st

    mkClss (_, RApp c ts _ _) | isClass c = classBinds emb (rRCls c ts)
    mkClss (x, t)                         = [(x, rSort t)]

    rSort   = rTypeSortedReft emb
    cmpZero e = F.PAtom F.Le (F.expr (0 :: Int)) (val e)

checkTy :: Bool
        -> BScope
        -> (Doc -> Error)
        -> F.TCEmb TyCon
        -> Bare.TyConMap
        -> F.SEnv F.SortedReft
        -> LocSpecType
        -> ElabM Diagnostics
checkTy allowHO bsc mkE emb tcEnv env t =
  do me <- checkRType allowHO bsc emb env (Bare.txRefSort tcEnv emb t)
     pure $ case me of
              Nothing -> emptyDiagnostics
              Just d  -> mkDiagnostics mempty [mkE d]
  where
    _msg =  "CHECKTY: " ++ showpp (val t)

checkDupIntersect     :: [(Var, LocSpecType)] -> [(Var, LocSpecType)] -> Diagnostics
checkDupIntersect xts asmSigs =
  mkDiagnostics (map mkWrn {- trace msg -} dups) mempty
  where
    mkWrn (x, t)   = mkWarning (GM.sourcePosSrcSpan $ loc t) (pprWrn x)
    dups           = L.intersectBy ((==) `on` fst) asmSigs xts
    pprWrn v       = text $ "Assume Overwrites Specifications for " ++ show v
    -- msg              = "CHECKDUPINTERSECT:" ++ msg1 ++ msg2
    -- msg1             = "\nCheckd-SIGS:\n" ++ showpp (M.fromList xts)
    -- msg2             = "\nAssume-SIGS:\n" ++ showpp (M.fromList asmSigs)


checkDuplicate :: [(Var, LocSpecType)] -> Diagnostics
checkDuplicate = mkDiagnostics mempty . checkUnique' fst (GM.fSrcSpan . snd)

checkClassMethods :: Maybe [ClsInst] -> [Var] ->  [(Var, LocSpecType)] -> Diagnostics
checkClassMethods Nothing      _   _   = emptyDiagnostics
checkClassMethods (Just clsis) cms xts =
  mkDiagnostics mempty [ErrMClass (GM.sourcePosSrcSpan $ loc t) (pprint x)| (x,t) <- dups ]
  where
    dups = F.notracepp "DPS" $ filter ((`elem` ms) . fst) xts'
    ms   = F.notracepp "MS"  $ concatMap (classMethods . is_cls) clsis
    xts' = F.notracepp "XTS" $ filter (not . (`elem` cls) . fst) xts
    cls  = F.notracepp "CLS" cms

checkDuplicateRTAlias :: String -> [Located (RTAlias s a)] -> Diagnostics
checkDuplicateRTAlias s tas = mkDiagnostics mempty (map mkError dups)
  where
    mkError xs@(x:_)          = ErrDupAlias (GM.fSrcSpan x)
                                          (text s)
                                          (pprint . rtName . val $ x)
                                          (GM.fSrcSpan <$> xs)
    mkError []                = panic Nothing "mkError: called on empty list"
    dups                    = [z | z@(_:_:_) <- groupDuplicatesOn (rtName . val) tas]

groupDuplicatesOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupDuplicatesOn f = L.groupBy ((==) `on` f) . L.sortOn f

checkMismatch        :: (Var, LocSpecType) -> Diagnostics
checkMismatch (x, t) = if ok then emptyDiagnostics else mkDiagnostics mempty [err]
  where
    ok               = tyCompat x (val t)
    err              = errTypeMismatch x t

tyCompat :: Var -> RType RTyCon RTyVar r -> Bool
tyCompat x t         = lqT == hsT
  where
    lqT :: RSort     = toRSort t
    hsT :: RSort     = ofType (varType x)
    _msg             = "TY-COMPAT: " ++ GM.showPpr x ++ ": hs = " ++ F.showpp hsT ++ " :lq = " ++ F.showpp lqT

errTypeMismatch     :: Var -> Located SpecType -> Error
errTypeMismatch x t = ErrMismatch lqSp (pprint x) (text "Checked")  d1 d2 Nothing hsSp
  where
    d1              = pprint $ varType x
    d2              = pprint $ toType False $ val t
    lqSp            = GM.fSrcSpan t
    hsSp            = getSrcSpan x

------------------------------------------------------------------------------------------------
-- | @checkRType@ determines if a type is malformed in a given environment ---------------------
------------------------------------------------------------------------------------------------
checkRType :: Bool -> BScope -> F.TCEmb TyCon -> F.SEnv F.SortedReft -> LocSpecType -> ElabM (Maybe Doc)
------------------------------------------------------------------------------------------------
checkRType allowHO bsc emb senv lt =
  do ef <- ask
     let f env me r err = err <|> runReader (checkReft (F.srcSpan lt) env emb me r) ef
     pure $     checkAppTys st
            <|> checkAbstractRefs st
            <|> efoldReft farg bsc cb (tyToBind emb) (rTypeSortedReft emb) f insertPEnv senv Nothing st
  where
    -- isErasable         = if allowTC then isEmbeddedDict else isClass
    st                 = val lt
    cb c ts            = classBinds emb (rRCls c ts)
    farg _ t           = allowHO || isBase t  -- NOTE: this check should be the same as the one in addCGEnv

    insertPEnv p γ     = insertsSEnv γ (fmap (rTypeSortedReft emb) <$> pbinds p)
    pbinds p           = (pname p, pvarRType p :: RSort) : [(x, tx) | (tx, x, _) <- pargs p]

tyToBind :: F.TCEmb TyCon -> RTVar RTyVar RSort  -> [(F.Symbol, F.SortedReft)]
tyToBind emb = go . ty_var_info
  where
    go RTVInfo{..} = [(rtv_name, rTypeSortedReft emb rtv_kind)]
    go RTVNoInfo{} = []

checkAppTys :: RType RTyCon t t1 -> Maybe Doc
checkAppTys = go
  where
    go (RAllT _ t _)    = go t
    go (RAllP _ t)      = go t
    go (RApp rtc ts _ _)
      = checkTcArity rtc (length ts) <|>
        L.foldl' (\merr t -> merr <|> go t) Nothing ts
    go (RFun _ _ t1 t2 _) = go t1 <|> go t2
    go (RVar _ _)       = Nothing
    go (RAllE _ t1 t2)  = go t1 <|> go t2
    go (REx _ t1 t2)    = go t1 <|> go t2
    go (RAppTy t1 t2 _) = go t1 <|> go t2
    go (RRTy _ _ _ t)   = go t
    go (RExprArg _)     = Just $ text "Logical expressions cannot appear inside a Haskell type"
    go (RHole _)        = Nothing

checkTcArity :: RTyCon -> Arity -> Maybe Doc
checkTcArity RTyCon{ rtc_tc = tc } givenArity
  | expectedArity < givenArity
    = Just $ text "Type constructor" <+> pprint tc
        <+> text "expects a maximum" <+> pprint expectedArity
        <+> text "arguments but was given" <+> pprint givenArity
        <+> text "arguments"
  | otherwise
    = Nothing
  where
    expectedArity = tyConRealArity tc


checkAbstractRefs
  :: (PPrint t, Reftable t, SubsTy RTyVar RSort t, Reftable (RTProp RTyCon RTyVar (UReft t))) =>
     RType RTyCon RTyVar (UReft t) -> Maybe Doc
checkAbstractRefs rt = go rt
  where
    penv = mkPEnv rt

    go t@(RAllT _ t1 r)   = check (toRSort t :: RSort) r <|>  go t1
    go (RAllP _ t)        = go t
    go t@(RApp c ts rs r) = check (toRSort t :: RSort) r <|>  efold go ts <|> go' c rs
    go t@(RFun _ _ t1 t2 r) = check (toRSort t :: RSort) r <|> go t1 <|> go t2
    go t@(RVar _ r)       = check (toRSort t :: RSort) r
    go (RAllE _ t1 t2)    = go t1 <|> go t2
    go (REx _ t1 t2)      = go t1 <|> go t2
    go t@(RAppTy t1 t2 r) = check (toRSort t :: RSort) r <|> go t1 <|> go t2
    go (RRTy xts _ _ t)   = efold go (snd <$> xts) <|> go t
    go (RExprArg _)       = Nothing
    go (RHole _)          = Nothing

    go' c rs = L.foldl' (\acc (x, y) -> acc <|> checkOne' x y) Nothing (zip rs (rTyConPVs c))

    checkOne' (RProp xs (RHole _)) p
      | or [s1 /= s2 | ((_, s1), (s2, _, _)) <- zip xs (pargs p)]
      = Just $ text "Wrong Arguments in" <+> pprint p
      | length xs /= length (pargs p)
      = Just $ text "Wrong Number of Arguments in" <+> pprint p
      | otherwise
      = Nothing
    checkOne' (RProp xs t) p
      | pvType p /= toRSort t
      = Just $ text "Unexpected Sort in" <+> pprint p
      | or [s1 /= s2 | ((_, s1), (s2, _, _)) <- zip xs (pargs p)]
      = Just $ text "Wrong Arguments in" <+> pprint p
      | length xs /= length (pargs p)
      = Just $ text "Wrong Number of Arguments in" <+> pprint p
      | otherwise
      = go t


    efold f = L.foldl' (\acc x -> acc <|> f x) Nothing

    check s (MkUReft _ (Pr ps)) = L.foldl' (\acc pp -> acc <|> checkOne s pp) Nothing ps

    checkOne s p | pvType' p /= s
                 = Just $ text "Incorrect Sort:\n\t"
                       <+> text "Abstract refinement with type"
                       <+> pprint (pvType' p)
                       <+> text "is applied to"
                       <+> pprint s
                       <+> text "\n\t In" <+> pprint p
                 | otherwise
                 = Nothing

    mkPEnv (RAllT _ t _) = mkPEnv t
    mkPEnv (RAllP p t)   = p:mkPEnv t
    mkPEnv _             = []
    pvType' p          = Misc.safeHead (showpp p ++ " not in env of " ++ showpp rt) [pvType q | q <- penv, pname p == pname q]


checkReft                    :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r, Reftable (RTProp RTyCon RTyVar (UReft r)))
                             => F.SrcSpan -> F.SEnv F.SortedReft -> F.TCEmb TyCon -> Maybe (RRType (UReft r)) -> UReft r -> ElabM (Maybe Doc)
checkReft _  _   _   Nothing  _ = pure Nothing -- TODO:RPropP/Ref case, not sure how to check these yet.
checkReft sp env emb (Just t) _ = do me <- checkSortedReftFull sp env r
                                     pure $ (\z -> dr $+$ z) <$> me
  where
    r                           = rTypeSortedReft emb t
    dr                          = text "Sort Error in Refinement:" <+> pprint r

-- DONT DELETE the below till we've added pred-checking as well
-- checkReft env emb (Just t) _ = checkSortedReft env xs (rTypeSortedReft emb t)
--    where xs                  = fromMaybe [] $ params <$> stripRTypeBase t

-- checkSig env (x, t)
--   = case filter (not . (`S.member` env)) (freeSymbols t) of
--       [] -> TrueNGUAGE ScopedTypeVariables #-}
--       ys -> errorstar (msg ys)
--     where
--       msg ys = printf "Unkown free symbols: %s in specification for %s \n%s\n" (showpp ys) (showpp x) (showpp t)

---------------------------------------------------------------------------------------------------
-- | @checkMeasures@ determines if a measure definition is wellformed -----------------------------
---------------------------------------------------------------------------------------------------
checkMeasures :: F.TCEmb TyCon -> F.SEnv F.SortedReft -> [Measure SpecType DataCon] -> ElabM Diagnostics
---------------------------------------------------------------------------------------------------
checkMeasures emb env = foldMapM (checkMeasure emb env)

checkMeasure :: F.TCEmb TyCon -> F.SEnv F.SortedReft -> Measure SpecType DataCon -> ElabM Diagnostics
checkMeasure emb γ (M name@(Loc src _ n) sort body _ _)
  = do me <- traverse (checkMBody γ emb name sort) body
       pure $ mkDiagnostics mempty [ txerror e | Just e <- me ]
  where
    txerror = ErrMeas (GM.sourcePosSrcSpan src) (pprint n)

checkMBody :: (PPrint r, Reftable r,SubsTy RTyVar RSort r, Reftable (RTProp RTyCon RTyVar r))
           => F.SEnv F.SortedReft
           -> F.TCEmb TyCon
           -> t
           -> SpecType
           -> Def (RRType r) DataCon
           -> ElabM (Maybe Doc)
checkMBody senv emb _ sort (Def m c _ bs body) = checkMBody' emb sort γ' sp body
  where
    sp    = F.srcSpan m
    γ'    = L.foldl' (\γ (x, t) -> F.insertSEnv x t γ) senv xts
    xts   = zip (fst <$> bs) $ rTypeSortedReft emb . subsTyVarsMeet su  <$>
            filter keep (ty_args trep)
    keep | allowTC = not . isEmbeddedClass
         | otherwise = not . isClassType
    -- YL: extract permitTC information from sort
    allowTC = any (fromMaybe False . permitTC) (ty_info $ toRTypeRep sort)
    trep  = toRTypeRep ct
    su    = checkMBodyUnify (ty_res trep) (last txs)
    txs   = thd5 $ bkArrowDeep sort
    ct    = ofType $ dataConWrapperType c :: SpecType

checkMBodyUnify
  :: RType t t2 t1 -> RType c tv r -> [(t2,RType c tv (),RType c tv r)]
checkMBodyUnify = go
  where
    go (RVar tv _) t      = [(tv, toRSort t, t)]
    go t@RApp{} t'@RApp{} = concat $ zipWith go (rt_args t) (rt_args t')
    go _ _                = []

checkMBody' :: (PPrint r, Reftable r, SubsTy RTyVar RSort r, Reftable (RTProp RTyCon RTyVar r))
            => F.TCEmb TyCon
            -> RType RTyCon RTyVar r
            -> F.SEnv F.SortedReft
            -> F.SrcSpan
            -> Body
            -> ElabM (Maybe Doc)
checkMBody' emb sort γ sp body =
  case body of
    E e   -> checkSortFull sp γ (rTypeSort emb sort') e
    P p   -> checkSortFull sp γ F.boolSort  p
    R s p -> checkSortFull sp (F.insertSEnv s sty γ) F.boolSort p
  where
    sty   = rTypeSortedReft emb sort'
    sort' = dropNArgs 1 sort

dropNArgs :: Int -> RType RTyCon RTyVar r -> RType RTyCon RTyVar r
dropNArgs i t = fromRTypeRep $ trep {ty_binds = xs, ty_info = is, ty_args = ts, ty_refts = rs}
  where
    xs   = drop i $ ty_binds trep
    ts   = drop i $ ty_args  trep
    rs   = drop i $ ty_refts trep
    is   = drop i $ ty_info trep
    trep = toRTypeRep t


getRewriteErrors :: (Var, Located SpecType) -> [TError t]
getRewriteErrors (rw, t)
  | null $ refinementEQs t
  = [ErrRewrite (GM.fSrcSpan t) $ text $
                "Unable to use "
                ++ show rw
                ++ " as a rewrite because it does not prove an equality, or the equality it proves is trivial." ]
  | otherwise
  = refErrs ++
      [ ErrRewrite (GM.fSrcSpan t) $
        text $ "Could not generate any rewrites from equality. Likely causes: "
        ++ "\n - There are free (uninstantiatable) variables on both sides of the "
        ++ "equality\n - The rewrite would diverge"
      | cannotInstantiate]
    where
        refErrs = map getInnerRefErr (filter (hasInnerRefinement . fst) (zip tyArgs syms))
        allowedRWs = [ (lhs, rhs) | (lhs , rhs) <- refinementEQs t
                 , canRewrite (S.fromList syms) lhs rhs ||
                   canRewrite (S.fromList syms) rhs lhs
                 ]
        cannotInstantiate = null allowedRWs
        tyArgs = ty_args  tRep
        syms   = ty_binds tRep
        tRep   = toRTypeRep $ val t
        getInnerRefErr (_, sym) =
          ErrRewrite (GM.fSrcSpan t) $ text $
          "Unable to use "
          ++ show rw
          ++ " as a rewrite. Functions whose parameters have inner refinements cannot be used as rewrites, but parameter "
          ++ show sym
          ++ " contains an inner refinement."


isRefined :: Reftable r => RType c tv r -> Bool
isRefined ty
  | Just r <- stripRTypeBase ty = not $ isTauto r
  | otherwise = False

hasInnerRefinement :: Reftable r => RType c tv r -> Bool
hasInnerRefinement (RFun _ _ rIn rOut _) =
  isRefined rIn || isRefined rOut
hasInnerRefinement (RAllT _ ty  _) =
  isRefined ty
hasInnerRefinement (RAllP _ ty) =
  isRefined ty
hasInnerRefinement (RApp _ args _ _) =
  any isRefined args
hasInnerRefinement (RAllE _ allarg ty) =
  isRefined allarg || isRefined ty
hasInnerRefinement (REx _ allarg ty) =
  isRefined allarg || isRefined ty
hasInnerRefinement (RAppTy arg res _) =
  isRefined arg || isRefined res
hasInnerRefinement (RRTy env _ _ ty) =
  isRefined ty || any (isRefined . snd) env
hasInnerRefinement _ = False

checkRewrites :: TargetSpec -> Diagnostics
checkRewrites targetSpec = mkDiagnostics mempty (concatMap getRewriteErrors rwSigs)
  where
    rwSigs = filter ((`S.member` rws) . fst) sigs
    refl   = gsRefl targetSpec
    sig    = gsSig targetSpec
    sigs   = gsTySigs sig ++ gsAsmSigs sig
    rws    = S.union (S.map val $ gsRewrites refl)
                   (S.fromList $ concat $ M.elems (gsRewritesWith refl))


checkClassMeasures :: [Measure SpecType DataCon] -> Diagnostics
checkClassMeasures measures = mkDiagnostics mempty (mapMaybe checkOne byTyCon)
  where
  byName = groupDuplicatesOn (val . msName) measures

  byTyCon = concatMap (groupDuplicatesOn (dataConTyCon . ctor . head . msEqns))
                      byName

  checkOne []     = impossible Nothing "checkClassMeasures.checkOne on empty measure group"
  checkOne [_]    = Nothing
  checkOne (m:ms) = Just (ErrDupIMeas (GM.fSrcSpan (msName m))
                                      (pprint (val (msName m)))
                                      (pprint ((dataConTyCon . ctor . head . msEqns) m))
                                      (GM.fSrcSpan <$> (m:ms)))



