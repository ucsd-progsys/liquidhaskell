{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.Haskell.Liquid.Bare.Check 
  ( checkGhcSpec
  , checkBareSpec
  , checkTy
  , checkTerminationExpr
  ) where

import           BasicTypes
import           DataCon
import           Id
import           Name                                      (getSrcSpan)
import           Prelude                                   hiding (error)
import           TyCon
import           Var
import qualified SrcLoc
import           Language.Haskell.Liquid.GHC.TypeRep (Type(TyConApp, TyVarTy))

import           Control.Applicative                       ((<|>))
import           Control.Arrow                             ((&&&))

import           Data.Maybe
import           Data.Function                             (on)
import           Text.PrettyPrint.HughesPJ

import qualified Data.List                                 as L
import qualified Data.HashMap.Strict                       as M
import qualified Data.HashSet                              as S
import           Data.Hashable
import qualified Language.Fixpoint.Misc                    as Misc  --(applyNonNull, group, safeHead, mapSnd)
import           Language.Fixpoint.SortCheck               (checkSorted, checkSortedReftFull, checkSortFull)
import qualified Language.Fixpoint.Types                   as F -- hiding (DataCtor, DataDecl, panic, Error, R)
import qualified Language.Haskell.Liquid.GHC.Misc          as GM -- (showPpr, fSrcSpan, sourcePosSrcSpan)
import           Language.Haskell.Liquid.Misc              (condNull, snd4)
import           Language.Haskell.Liquid.Types.PredType    (pvarRType)
import           Language.Haskell.Liquid.Types.PrettyPrint (pprintSymbol)
import           Language.Haskell.Liquid.Types.RefType     (classBinds, ofType, rTypeSort, rTypeSortedReft, subsTyVars_meet, toType)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure           as Ms
import qualified Language.Haskell.Liquid.Bare.Types        as Bare 
import qualified Language.Haskell.Liquid.Bare.Resolve      as Bare 

-- import           Language.Haskell.Liquid.Bare.Env
-- import           Language.Haskell.Liquid.Bare.SymSort      (txRefSort)

import           Debug.Trace (trace)

----------------------------------------------------------------------------------------------
-- | Checking BareSpec ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------
checkBareSpec :: ModName -> Ms.BareSpec -> Either [Error] Ms.BareSpec 
checkBareSpec _ sp = Misc.applyNonNull (Right sp) Left $ concat 
  [ checkUnique   "measure"    measures 
  , checkUnique   "field"      fields 
  , checkDisjoints             [ inlines
                               , hmeasures
                               , S.fromList measures
                               , reflects
                               , S.fromList fields 
                               ]  
  ] 
  where 
    inlines   = Ms.inlines    sp 
    hmeasures = Ms.hmeas      sp 
    reflects  = Ms.reflects   sp 
    measures  = msName    <$> Ms.measures sp 
    fields    = concatMap dataDeclFields (Ms.dataDecls sp) 

dataDeclFields :: DataDecl -> [F.LocSymbol]
dataDeclFields = Misc.hashNubWith val . concatMap dataCtorFields . tycDCons

dataCtorFields :: DataCtor -> [F.LocSymbol]
dataCtorFields c 
  | isGadt c  = [] 
  | otherwise = F.atLoc c <$> [ f | (f,_) <- dcFields c ]

isGadt :: DataCtor -> Bool 
isGadt = isJust . dcResult 

checkUnique :: String -> [F.LocSymbol] -> [Error]
checkUnique _ = checkUnique' F.val GM.fSrcSpan 

checkUnique' :: (PPrint a, Eq a, Hashable a) 
             => (t -> a) -> (t -> SrcLoc.SrcSpan) -> [t] -> [Error]
checkUnique' nameF locF ts = mkErr <$> dups
  where
    mkErr (n, ls@(l:_))    = ErrDupSpecs l (pprint n) ls
    dups                   = [ z      | z@(_, _:_:_) <- Misc.groupList nts       ] 
    nts                    = [ (n, l) | t <- ts, let n = nameF t, let l = locF t ]

checkDisjoints :: [S.HashSet F.LocSymbol] -> [Error]
checkDisjoints []     = [] 
checkDisjoints [_]    = [] 
checkDisjoints (s:ss) = checkDisjoint s (S.unions ss) 
                     ++ checkDisjoints ss 

checkDisjoint :: S.HashSet F.LocSymbol -> S.HashSet F.LocSymbol -> [Error]
checkDisjoint s1 s2 = checkUnique "disjoint" (S.toList s1 ++ S.toList s2) 

----------------------------------------------------------------------------------------------
-- | Checking GhcSpec ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------

checkGhcSpec :: [(ModName, Ms.BareSpec)]
             -> F.SEnv F.SortedReft
             -> GhcSpec
             -> Either [Error] GhcSpec

checkGhcSpec specs env sp = Misc.applyNonNull (Right sp) Left errors
  where
    errors           =  mapMaybe (checkBind allowHO "measure"      emb tcEnv env) (gsMeas       (gsData sp))
                     ++ condNull noPrune
                       (mapMaybe (checkBind allowHO "constructor"  emb tcEnv env) (gsCtors      (gsData sp)))
                     ++ mapMaybe (checkBind allowHO "assumed type" emb tcEnv env) (gsAsmSigs    (gsSig sp))
                     ++ mapMaybe (checkBind allowHO "class method" emb tcEnv env) (clsSigs      (gsSig sp))
                     ++ mapMaybe (checkInv allowHO emb tcEnv env)                 (gsInvariants (gsData sp))
                     ++ checkIAl allowHO emb tcEnv env                            (gsIaliases   (gsData sp))
                     ++ checkMeasures emb env ms
                     ++ checkClassMeasures                                        (gsMeasures (gsData sp))
                     ++ mapMaybe checkMismatch                     sigs
                     ++ checkDuplicate                                            (gsTySigs     (gsSig sp))
                     -- ++ checkQualifiers env                                       (gsQualifiers (gsQual sp))
                     ++ checkDuplicate                                            (gsAsmSigs    (gsSig sp))
                     ++ checkDupIntersect                                         (gsTySigs (gsSig sp)) (gsAsmSigs (gsSig sp))
                     ++ checkRTAliases "Type Alias" env            tAliases
                     ++ checkRTAliases "Pred Alias" env            eAliases
                     -- ++ _checkDuplicateFieldNames                   (gsDconsP sp)
                     -- NV TODO: allow instances of refined classes to be refined
                     -- but make sure that all the specs are checked.
                     -- ++ checkRefinedClasses                        rClasses rInsts
                     ++ checkSizeFun emb env                                      (gsTconsP (gsName sp))
    _rClasses         = concatMap (Ms.classes   . snd) specs
    _rInsts           = concatMap (Ms.rinstance . snd) specs
    tAliases          = concat [Ms.aliases sp  | (_, sp) <- specs]
    eAliases          = concat [Ms.ealiases sp | (_, sp) <- specs]
    emb              = gsTcEmbeds (gsName sp)
    tcEnv            = gsTyconEnv (gsName sp)
    ms               = gsMeasures (gsData sp)
    clsSigs sp       = [ (v, t) | (v, t) <- gsTySigs sp, isJust (isClassOpId_maybe v) ]
    sigs             = gsTySigs (gsSig sp) ++ gsAsmSigs (gsSig sp)
    allowHO          = higherOrderFlag sp
    noPrune          = not (pruneFlag sp)
    -- env'             = L.foldl' (\e (x, s) -> insertSEnv x (RR s mempty) e) env wiredSortedSyms


checkQualifiers :: F.SEnv F.SortedReft -> [F.Qualifier] -> [Error]
checkQualifiers = mapMaybe . checkQualifier

checkQualifier       :: F.SEnv F.SortedReft -> F.Qualifier -> Maybe Error
checkQualifier env q =  mkE <$> checkSortFull (F.srcSpan q) γ F.boolSort  (F.qBody q)
  where 
    γ                = L.foldl' (\e (x, s) -> F.insertSEnv x (F.RR s mempty) e) env (F.qualBinds q ++ wiredSortedSyms)
    mkE              = ErrBadQual (GM.fSrcSpan q) (pprint $ F.qName q)

checkSizeFun :: F.TCEmb TyCon -> F.SEnv F.SortedReft -> [TyConP] -> [Error]
checkSizeFun emb env tys = mkError <$> mapMaybe go tys
  where
    mkError ((f, tcp), msg)  = ErrTyCon (GM.sourcePosSrcSpan $ tcpLoc tcp)
                                 (text "Size function" <+> pprint (f x) <+> text "should have type int." $+$   msg)
                                 (pprint (tcpCon tcp))
    go tcp = case tcpSizeFun tcp of
               Nothing  -> Nothing
               Just f   -> checkWFSize (szFun f) tcp

    checkWFSize f tcp = ((f, tcp),) <$> checkSortFull (F.srcSpan tcp) (F.insertSEnv x (mkTySort (tcpCon tcp)) env) F.intSort (f x)
    x                 = "x" :: F.Symbol
    mkTySort tc       = rTypeSortedReft emb (ofType $ TyConApp tc (TyVarTy <$> tyConTyVars tc) :: RRType ())

_checkRefinedClasses :: [RClass LocBareType] -> [RInstance LocBareType] -> [Error]
_checkRefinedClasses definitions instances
  = mkError <$> duplicates
  where
    duplicates
      = mapMaybe checkCls (rcName <$> definitions)
    checkCls cls
      = case findConflicts cls of
          []        -> Nothing
          conflicts -> Just (cls, conflicts)
    findConflicts cls
      = filter ((== cls) . riclass) instances

    mkError (cls, conflicts)
      = ErrRClass (GM.sourcePosSrcSpan $ loc $ btc_tc cls)
                  (pprint cls) (ofConflict <$> conflicts)
    ofConflict
      = GM.sourcePosSrcSpan . loc . btc_tc . riclass &&& pprint . ritype

_checkDuplicateFieldNames :: [(DataCon, DataConP)]  -> [Error]
_checkDuplicateFieldNames = mapMaybe go
  where
    go (d, dts)          = checkNoDups (dcpLoc dts) d (fst <$> dcpTyArgs dts)
    checkNoDups l d xs   = mkErr l d <$> _firstDuplicate xs

    mkErr l d x = ErrBadData (GM.sourcePosSrcSpan l)
                             (pprint d)
                             (text "Multiple declarations of record selector" <+> pprintSymbol x)

_firstDuplicate :: Ord a => [a] -> Maybe a
_firstDuplicate = go . L.sort
  where
    go (y:x:xs) | x == y    = Just x
                | otherwise = go (x:xs)
    go _                    = Nothing

checkInv :: Bool -> F.TCEmb TyCon -> Bare.TyConMap -> F.SEnv F.SortedReft -> (Maybe Var, LocSpecType) -> Maybe Error
checkInv allowHO emb tcEnv env (_, t) = checkTy allowHO err emb tcEnv env t
  where
    err              = ErrInvt (GM.sourcePosSrcSpan $ loc t) (val t)

checkIAl :: Bool -> F.TCEmb TyCon -> Bare.TyConMap -> F.SEnv F.SortedReft -> [(LocSpecType, LocSpecType)] -> [Error]
checkIAl allowHO emb tcEnv env ials = catMaybes $ concatMap (checkIAlOne allowHO emb tcEnv env) ials

checkIAlOne :: Bool
            -> F.TCEmb TyCon
            -> Bare.TyConMap
            -> F.SEnv F.SortedReft
            -> (LocSpecType, LocSpecType)
            -> [Maybe (TError SpecType)]
checkIAlOne allowHO emb tcEnv env (t1, t2) = checkEq : (tcheck <$> [t1, t2])
  where
    tcheck t = checkTy allowHO (err t) emb tcEnv env t
    err    t = ErrIAl (GM.sourcePosSrcSpan $ loc t) (val t)
    t1'      :: RSort
    t1'      = toRSort $ val t1
    t2'      :: RSort
    t2'      = toRSort $ val t2
    checkEq  = if t1' == t2' then Nothing else Just errmis
    errmis   = ErrIAlMis (GM.sourcePosSrcSpan $ loc t1) (val t1) (val t2) emsg
    emsg     = pprint t1 <+> text "does not match with" <+> pprint t2


-- FIXME: Should _ be removed if it isn't used?
checkRTAliases :: String -> t -> [Located (RTAlias s a)] -> [Error]
checkRTAliases msg _ as = err1s
  where
    err1s               = checkDuplicateRTAlias msg as

checkBind :: (PPrint v) => Bool -> String -> F.TCEmb TyCon -> Bare.TyConMap -> F.SEnv F.SortedReft -> (v, LocSpecType) -> Maybe Error
checkBind allowHO s emb tcEnv env (v, t) = checkTy allowHO msg emb tcEnv env t
  where
    msg                      = ErrTySpec (GM.fSrcSpan t) (text s <+> pprint v) (val t)

checkTerminationExpr :: (Eq v, PPrint v) => F.TCEmb TyCon -> F.SEnv F.SortedReft -> (v, LocSpecType, [F.Located F.Expr]) -> Maybe Error
checkTerminationExpr emb env (v, Loc l _ t, les)
            = (mkErr <$> go les) <|> (mkErr' <$> go' les)
  where
    -- es      = val <$> les
    mkErr   = uncurry (ErrTermSpec (GM.sourcePosSrcSpan l) (pprint v) (text "ill-sorted" ))
    mkErr'  = uncurry (ErrTermSpec (GM.sourcePosSrcSpan l) (pprint v) (text "non-numeric"))
    go      = L.foldl' (\err e -> err <|> (val e,) <$> checkSorted (F.srcSpan e) env' (val e))           Nothing
    go'     = L.foldl' (\err e -> err <|> (val e,) <$> checkSorted (F.srcSpan e) env' (cmpZero e)) Nothing
    env'    = F.sr_sort <$> L.foldl' (\e (x,s) -> F.insertSEnv x s e) env xts
    xts     = concatMap mkClass $ zip (ty_binds trep) (ty_args trep)
    trep    = toRTypeRep t

    mkClass (_, RApp c ts _ _) | isClass c = classBinds emb (rRCls c ts)
    mkClass (x, t)                         = [(x, rSort t)]

    rSort   = rTypeSortedReft emb
    cmpZero e = F.PAtom F.Le (F.expr (0 :: Int)) (val e)

checkTy :: Bool -> (Doc -> Error) -> F.TCEmb TyCon -> Bare.TyConMap -> F.SEnv F.SortedReft -> LocSpecType -> Maybe Error
checkTy allowHO mkE emb tcEnv env t = mkE <$> checkRType allowHO emb env (Bare.txRefSort tcEnv emb t)
  where
    _msg =  "CHECKTY: " ++ showpp (val t)

checkDupIntersect     :: [(Var, LocSpecType)] -> [(Var, LocSpecType)] -> [Error]
checkDupIntersect xts asmSigs = concatMap mkWrn {- trace msg -} dups
  where
    mkWrn (x, t)     = pprWrn x (GM.sourcePosSrcSpan $ loc t)
    dups             = L.intersectBy ((==) `on` fst) asmSigs xts
    pprWrn v l       = trace ("WARNING: Assume Overwrites Specifications for "++ show v ++ " : " ++ GM.showPpr l) []
    -- msg              = "CHECKDUPINTERSECT:" ++ msg1 ++ msg2
    -- msg1             = "\nCheckd-SIGS:\n" ++ showpp (M.fromList xts)
    -- msg2             = "\nAssume-SIGS:\n" ++ showpp (M.fromList asmSigs)

checkDuplicate :: [(Var, LocSpecType)] -> [Error]
checkDuplicate = checkUnique' fst (GM.fSrcSpan . snd)

-- checkDuplicate xts = mkErr <$> dups
  -- where
    -- mkErr (x, ts) = ErrDupSpecs (getSrcSpan x) (pprint x) (GM.fSrcSpan <$> ts)
    -- dups          = [z | z@(_, _:_:_) <- M.toList $ group xts ]


checkDuplicateRTAlias :: String -> [Located (RTAlias s a)] -> [Error]
checkDuplicateRTAlias s tas = mkErr <$> dups
  where
    mkErr xs@(x:_)          = ErrDupAlias (GM.fSrcSpan x)
                                          (text s)
                                          (pprint . rtName . val $ x)
                                          (GM.fSrcSpan <$> xs)
    mkErr []                = panic Nothing "mkError: called on empty list"
    dups                    = [z | z@(_:_:_) <- L.groupBy ((==) `on` (rtName . val)) tas]


checkMismatch        :: (Var, Located SpecType) -> Maybe Error
checkMismatch (x, t) = if ok then Nothing else Just err
  where
    ok               = tyCompat x (val t')
    err              = errTypeMismatch x t'
    t'               = dropImplicits <$> t

tyCompat :: Var -> RType RTyCon RTyVar r -> Bool
tyCompat x t         = lhs == rhs
  where
    lhs :: RSort     = toRSort t
    rhs :: RSort     = ofType $ varType x

errTypeMismatch     :: Var -> Located SpecType -> Error
errTypeMismatch x t = ErrMismatch lqSp (pprint x) (text "Checked")  d1 d2 hsSp
  where
    d1              = pprint $ varType x
    d2              = pprint $ toType $ val t
    lqSp            = GM.fSrcSpan t
    hsSp            = getSrcSpan x

------------------------------------------------------------------------------------------------
-- | @checkRType@ determines if a type is malformed in a given environment ---------------------
------------------------------------------------------------------------------------------------
checkRType :: Bool -> F.TCEmb TyCon -> F.SEnv F.SortedReft -> LocSpecType -> Maybe Doc
------------------------------------------------------------------------------------------------
checkRType allowHO emb env lt
  =   checkAppTys t
  <|> checkAbstractRefs t
  <|> efoldReft farg cb (tyToBind emb) (rTypeSortedReft emb) f insertPEnv env Nothing t
  where
    t                  = val lt
    cb c ts            = classBinds emb (rRCls c ts)
    farg _ t           = allowHO || isBase t  -- NOTE: this check should be the same as the one in addCGEnv
    f env me r err     = err <|> checkReft (F.srcSpan lt) env emb me r
    insertPEnv p γ     = insertsSEnv γ (Misc.mapSnd (rTypeSortedReft emb) <$> pbinds p)
    pbinds p           = (pname p, pvarRType p :: RSort) : [(x, tx) | (tx, x, _) <- pargs p]

tyToBind :: F.TCEmb TyCon -> RTVar RTyVar RSort  -> [(F.Symbol, F.SortedReft)]
tyToBind emb = go . ty_var_info
  where
    go (RTVInfo {..}) = [(rtv_name, rTypeSortedReft emb rtv_kind)]
    go RTVNoInfo      = []

checkAppTys :: RType RTyCon t t1 -> Maybe Doc
checkAppTys = go
  where
    go (RAllT _ t)      = go t
    go (RAllP _ t)      = go t
    go (RAllS _ t)      = go t
    go (RApp rtc ts _ _)
      = checkTcArity rtc (length ts) <|>
        L.foldl' (\merr t -> merr <|> go t) Nothing ts
    go (RImpF _ t1 t2 _)= go t1 <|> go t2
    go (RFun _ t1 t2 _) = go t1 <|> go t2
    go (RVar _ _)       = Nothing
    go (RAllE _ t1 t2)  = go t1 <|> go t2
    go (REx _ t1 t2)    = go t1 <|> go t2
    go (RAppTy t1 t2 _) = go t1 <|> go t2
    go (RRTy _ _ _ t)   = go t
    go (RExprArg _)     = Just $ text "Logical expressions cannot appear inside a Haskell type"
    go (RHole _)        = Nothing

checkTcArity :: RTyCon -> Arity -> Maybe Doc
checkTcArity (RTyCon { rtc_tc = tc }) givenArity
  | expectedArity < givenArity
    = Just $ text "Type constructor" <+> pprint tc
        <+> text "expects a maximum" <+> pprint expectedArity
        <+> text "arguments but was given" <+> pprint givenArity
        <+> text "arguments"
  | otherwise
    = Nothing
  where
    expectedArity = tyConArity tc

{-
checkFunRefs t = go t
  where
    go (RAllT _ t)      = go t
    go (RAllP _ t)      = go t
    go (RAllS _ t)      = go t
    go (RApp _ ts _ _)  = foldl (\merr t -> merr <|> go t) Nothing ts
    go (RVar _ _)       = Nothing
    go (RAllE _ t1 t2)  = go t1 <|> go t2
    go (REx _ t1 t2)    = go t1 <|> go t2
    go (RAppTy t1 t2 _) = go t1 <|> go t2
    go (RRTy _ _ _ t)   = go t
    go (RExprArg _)     = Nothing
    go (RHole _)        = Nothing
    go (RFun _ t1 t2 r)
      | isTauto r       = go t1 <|> go t2
      | otherwise       = Just $ text "Function types cannot have refinements:" <+> (pprint r)
-}

checkAbstractRefs
  :: (PPrint t, F.Reftable t, SubsTy RTyVar RSort t, F.Reftable (RTProp RTyCon RTyVar (UReft t))) =>
     RType RTyCon RTyVar (UReft t) -> Maybe Doc
checkAbstractRefs t = go t
  where
    penv = mkPEnv t

    go (RAllT _ t)        = go t
    go (RAllP _ t)        = go t
    go (RAllS _ t)        = go t
    go t@(RApp c ts rs r) = check (toRSort t :: RSort) r <|>  efold go ts <|> go' c rs
    go t@(RImpF _ t1 t2 r)= check (toRSort t :: RSort) r <|> go t1 <|> go t2
    go t@(RFun _ t1 t2 r) = check (toRSort t :: RSort) r <|> go t1 <|> go t2
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

    check s (MkUReft _ (Pr ps) _) = L.foldl' (\acc pp -> acc <|> checkOne s pp) Nothing ps

    checkOne s p | pvType' p /= s
                 = Just $ text "Incorrect Sort:\n\t"
                       <+> text "Abstract refinement with type"
                       <+> pprint (pvType' p)
                       <+> text "is applied to"
                       <+> pprint s
                       <+> text "\n\t In" <+> pprint p
                 | otherwise
                 = Nothing

    mkPEnv (RAllT _ t) = mkPEnv t
    mkPEnv (RAllP p t) = p:mkPEnv t
    mkPEnv _           = []
    pvType' p          = Misc.safeHead (showpp p ++ " not in env of " ++ showpp t) [pvType q | q <- penv, pname p == pname q]


checkReft                    :: (PPrint r, F.Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r, F.Reftable (RTProp RTyCon RTyVar (UReft r)))
                             => F.SrcSpan -> F.SEnv F.SortedReft -> F.TCEmb TyCon -> Maybe (RRType (UReft r)) -> UReft r -> Maybe Doc
checkReft _ _   _   Nothing _   = Nothing -- TODO:RPropP/Ref case, not sure how to check these yet.
checkReft sp env emb (Just t) _ = (\z -> dr $+$ z) <$> checkSortedReftFull sp env r
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
checkMeasures :: F.TCEmb TyCon -> F.SEnv F.SortedReft -> [Measure SpecType DataCon] -> [Error]
---------------------------------------------------------------------------------------------------
checkMeasures emb env = concatMap (checkMeasure emb env)

checkMeasure :: F.TCEmb TyCon -> F.SEnv F.SortedReft -> Measure SpecType DataCon -> [Error]
checkMeasure emb γ (M name@(Loc src _ n) sort body _)
  = [ txerror e | Just e <- checkMBody γ emb name sort <$> body ]
  where
    txerror = ErrMeas (GM.sourcePosSrcSpan src) (pprint n)

checkMBody :: (PPrint r, F.Reftable r,SubsTy RTyVar RSort r, F.Reftable (RTProp RTyCon RTyVar r))
           => F.SEnv F.SortedReft
           -> F.TCEmb TyCon
           -> t
           -> SpecType
           -> Def (RRType r) DataCon
           -> Maybe Doc
checkMBody γ emb _ sort (Def m c _ bs body) = checkMBody' emb sort γ' sp body
  where
    sp    = F.srcSpan m
    γ'    = L.foldl' (\γ (x, t) -> F.insertSEnv x t γ) γ xts
    xts   = zip (fst <$> bs) $ rTypeSortedReft emb . subsTyVars_meet su <$> ty_args trep
    trep  = toRTypeRep ct
    su    = checkMBodyUnify (ty_res trep) (last txs)
    txs   = snd4 $ bkArrowDeep sort
    ct    = ofType $ dataConUserType c :: SpecType

checkMBodyUnify
  :: RType t t2 t1 -> RType c tv r -> [(t2,RType c tv (),RType c tv r)]
checkMBodyUnify                 = go
  where
    go (RVar tv _) t            = [(tv, toRSort t, t)]
    go t@(RApp {}) t'@(RApp {}) = concat $ zipWith go (rt_args t) (rt_args t')
    go _ _                      = []

checkMBody' :: (PPrint r, F.Reftable r,SubsTy RTyVar RSort r, F.Reftable (RTProp RTyCon RTyVar r))
            => F.TCEmb TyCon
            -> RType RTyCon RTyVar r
            -> F.SEnv F.SortedReft
            -> F.SrcSpan 
            -> Body
            -> Maybe Doc
checkMBody' emb sort γ sp body = case body of
    E e   -> checkSortFull sp γ (rTypeSort emb sort') e
    P p   -> checkSortFull sp γ F.boolSort  p
    R s p -> checkSortFull sp (F.insertSEnv s sty γ) F.boolSort p
  where
    sty   = rTypeSortedReft emb sort'
    sort' = dropNArgs 1 sort

dropNArgs :: Int -> RType RTyCon RTyVar r -> RType RTyCon RTyVar r
dropNArgs i t = fromRTypeRep $ trep {ty_binds = xs, ty_args = ts, ty_refts = rs}
  where
    xs   = drop i $ ty_binds trep
    ts   = drop i $ ty_args  trep
    rs   = drop i $ ty_refts trep
    trep = toRTypeRep t


checkClassMeasures :: [Measure SpecType DataCon] -> [Error]
checkClassMeasures ms = mapMaybe checkOne byTyCon
  where
  byName = L.groupBy ((==) `on` (val . msName)) ms

  byTyCon = concatMap (L.groupBy ((==) `on` (dataConTyCon . ctor . head . msEqns)))
                      byName

  checkOne []     = impossible Nothing "checkClassMeasures.checkOne on empty measure group"
  checkOne [_]    = Nothing
  checkOne (m:ms) = Just (ErrDupIMeas (GM.fSrcSpan (msName m))
                                      (pprint (val (msName m)))
                                      (pprint ((dataConTyCon . ctor . head . msEqns) m))
                                      (GM.fSrcSpan <$> (m:ms)))



