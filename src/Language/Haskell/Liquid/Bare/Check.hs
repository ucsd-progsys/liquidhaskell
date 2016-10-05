{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE RecordWildCards     #-}

module Language.Haskell.Liquid.Bare.Check (
    checkGhcSpec

  , checkTerminationExpr
  , checkTy
  ) where

import           BasicTypes
import           DataCon
import           Id
import           Name                                      (getSrcSpan)
import           Prelude                                   hiding (error)
import           TyCon
import           Var

import           Control.Applicative                       ((<|>))
import           Control.Arrow                             ((&&&))

import           Data.Maybe
import           Data.Function                             (on)
import           Text.PrettyPrint.HughesPJ

import qualified Data.List                                 as L
import qualified Data.HashMap.Strict                       as M

import           Language.Fixpoint.Misc                    (applyNonNull, group, safeHead, mapSnd)
import           Language.Fixpoint.SortCheck               (checkSorted, checkSortedReftFull, checkSortFull)
import           Language.Fixpoint.Types                   hiding (Error, R)

import           Language.Haskell.Liquid.GHC.Misc          (realTcArity, showPpr, fSrcSpan, sourcePosSrcSpan)
import           Language.Haskell.Liquid.Misc              (snd4)
import           Language.Haskell.Liquid.Types.PredType    (pvarRType)
import           Language.Haskell.Liquid.Types.PrettyPrint (pprintSymbol)
import           Language.Haskell.Liquid.Types.RefType     (classBinds, ofType, rTypeSort, rTypeSortedReft, subsTyVars_meet, toType)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.WiredIn



import qualified Language.Haskell.Liquid.Measure           as Ms

import           Language.Haskell.Liquid.Bare.DataType     (dataConSpec)
import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.SymSort      (txRefSort)

import           Debug.Trace (trace)


----------------------------------------------------------------------------------------------
----- Checking GhcSpec -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------

checkGhcSpec :: [(ModName, Ms.BareSpec)]
             -> SEnv SortedReft
             -> GhcSpec
             -> Either [Error] GhcSpec

checkGhcSpec specs env sp =  applyNonNull (Right sp) Left errors
  where
    errors           =  mapMaybe (checkBind allowHO "constructor"  emb tcEnv env) (dcons      sp)
                     ++ mapMaybe (checkBind allowHO "measure"      emb tcEnv env) (gsMeas       sp)
                     ++ mapMaybe (checkBind allowHO "assumed type" emb tcEnv env) (gsAsmSigs    sp)
                     ++ mapMaybe (checkBind allowHO "class method" emb tcEnv env) (clsSigs    sp)
                     ++ mapMaybe (checkInv allowHO emb tcEnv env)                 (gsInvariants sp)
                     ++ checkIAl allowHO emb tcEnv env (gsIaliases   sp)
                     ++ checkMeasures emb env ms
                     ++ checkClassMeasures (gsMeasures sp)
                     ++ mapMaybe checkMismatch                     sigs
                     ++ checkDuplicate                             (gsTySigs sp)
                     ++ checkQualifiers env                        (gsQualifiers sp)
                     ++ checkDuplicate                             (gsAsmSigs sp)
                     ++ checkDupIntersect                          (gsTySigs sp) (gsAsmSigs sp)
                     ++ checkRTAliases "Type Alias" env            tAliases
                     ++ checkRTAliases "Pred Alias" env            eAliases
                     ++ checkDuplicateFieldNames                   (gsDconsP sp)
                     ++ checkRefinedClasses                        rClasses rInsts
    rClasses         = concatMap (Ms.classes   . snd) specs
    rInsts           = concatMap (Ms.rinstance . snd) specs
    tAliases         = concat [Ms.aliases sp  | (_, sp) <- specs]
    eAliases         = concat [Ms.ealiases sp | (_, sp) <- specs]
    dcons spec       = [(v, Loc l l' t) | (v, t)   <- dataConSpec (gsDconsP spec)
                                        | (_, dcp) <- gsDconsP spec
                                        , let l     = dc_loc  dcp
                                        , let l'    = dc_locE dcp ]
    emb              = gsTcEmbeds sp
    tcEnv            = gsTyconEnv sp
    ms               = gsMeasures sp
    clsSigs sp       = [ (v, t) | (v, t) <- gsTySigs sp, isJust (isClassOpId_maybe v) ]
    sigs             = gsTySigs sp ++ gsAsmSigs sp
    allowHO          = higherOrderFlag sp


checkQualifiers :: SEnv SortedReft -> [Qualifier] -> [Error]
checkQualifiers = mapMaybe . checkQualifier

checkQualifier       :: SEnv SortedReft -> Qualifier -> Maybe Error
checkQualifier env q =  mkE <$> checkSortFull γ boolSort  (qBody q)
  where γ   = foldl (\e (x, s) -> insertSEnv x (RR s mempty) e) env (qParams q ++ wiredSortedSyms)
        mkE = ErrBadQual (sourcePosSrcSpan $ qPos q) (pprint $ qName q)

checkRefinedClasses :: [RClass (Located BareType)] -> [RInstance (Located BareType)] -> [Error]
checkRefinedClasses definitions instances
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
      = ErrRClass (sourcePosSrcSpan $ loc $ btc_tc cls)
                  (pprint cls) (ofConflict <$> conflicts)
    ofConflict
      = sourcePosSrcSpan . loc . btc_tc . riclass &&& pprint . ritype

checkDuplicateFieldNames :: [(DataCon, DataConP)]  -> [Error]
checkDuplicateFieldNames = mapMaybe go
  where
    go (d, dts)          = checkNoDups (dc_loc dts) d (fst <$> tyArgs dts)
    checkNoDups l d xs   = mkErr l d <$> firstDuplicate xs

    mkErr l d x = ErrBadData (sourcePosSrcSpan l)
                             (pprint d)
                             (text "Multiple declarations of record selector" <+> pprintSymbol x)

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go . L.sort
  where
    go (y:x:xs) | x == y    = Just x
                | otherwise = go (x:xs)
    go _                    = Nothing

checkInv :: Bool -> TCEmb TyCon -> TCEnv -> SEnv SortedReft -> (Maybe Var, Located SpecType) -> Maybe Error
checkInv allowHO emb tcEnv env (_, t)   = checkTy allowHO err emb tcEnv env t
  where
    err              = ErrInvt (sourcePosSrcSpan $ loc t) (val t)

checkIAl :: Bool -> TCEmb TyCon -> TCEnv -> SEnv SortedReft -> [(Located SpecType, Located SpecType)] -> [Error]
checkIAl allowHO emb tcEnv env ials = catMaybes $ concatMap (checkIAlOne allowHO emb tcEnv env) ials

checkIAlOne :: Bool
            -> TCEmb TyCon
            -> TCEnv
            -> SEnv SortedReft
            -> (Located SpecType, Located SpecType)
            -> [Maybe (TError SpecType)]
checkIAlOne allowHO emb tcEnv env (t1, t2) = checkEq : (tcheck <$> [t1, t2])
  where
    tcheck t = checkTy allowHO (err t) emb tcEnv env t
    err    t = ErrIAl (sourcePosSrcSpan $ loc t) (val t)
    t1'      :: RSort
    t1'      = toRSort $ val t1
    t2'      :: RSort
    t2'      = toRSort $ val t2
    checkEq  = if t1' == t2' then Nothing else Just errmis
    errmis   = ErrIAlMis (sourcePosSrcSpan $ loc t1) (val t1) (val t2) emsg
    emsg     = pprint t1 <+> text "does not match with" <+> pprint t2


-- FIXME: Should _ be removed if it isn't used?
checkRTAliases :: String -> t -> [RTAlias s a] -> [Error]
checkRTAliases msg _ as = err1s
  where
    err1s                  = checkDuplicateRTAlias msg as

checkBind :: (PPrint v) => Bool -> String -> TCEmb TyCon -> TCEnv -> SEnv SortedReft -> (v, Located SpecType) -> Maybe Error
checkBind allowHO s emb tcEnv env (v, t) = checkTy allowHO msg emb tcEnv env' t
  where
    msg                      = ErrTySpec (fSrcSpan t) (text s <+> pprint v) (val t)
    env'                     = foldl (\e (x, s) -> insertSEnv x (RR s mempty) e) env wiredSortedSyms

checkTerminationExpr :: (Eq v, PPrint v) => TCEmb TyCon -> SEnv SortedReft -> (v, LocSpecType, [Located Expr])-> Maybe Error
checkTerminationExpr emb env (v, Loc l _ t, les)
            = (mkErr <$> go es) <|> (mkErr' <$> go' es)
  where
    es      = val <$> les
    mkErr   = uncurry (ErrTermSpec (sourcePosSrcSpan l) (text "termination expression" <+> pprint v))
    mkErr'  = uncurry (ErrTermSpec (sourcePosSrcSpan l) (text "termination expression is not numeric"))
    go      = foldl (\err e -> err <|> (e,) <$> checkSorted env' e)           Nothing
    go'     = foldl (\err e -> err <|> (e,) <$> checkSorted env' (cmpZero e)) Nothing
    env'    = foldl (\e (x, s) -> insertSEnv x s e) env'' wiredSortedSyms
    env''   = sr_sort <$> foldl (\e (x,s) -> insertSEnv x s e) env xts
    xts     = concatMap mkClass $ zip (ty_binds trep) (ty_args trep)
    trep    = toRTypeRep t

    mkClass (_, RApp c ts _ _) | isClass c = classBinds (rRCls c ts)
    mkClass (x, t)                         = [(x, rSort t)]

    rSort   = rTypeSortedReft emb
    cmpZero = PAtom Le $ expr (0 :: Int) -- zero

checkTy :: Bool -> (Doc -> Error) -> TCEmb TyCon -> TCEnv -> SEnv SortedReft -> Located SpecType -> Maybe Error
checkTy allowHO mkE emb tcEnv env t = mkE <$> checkRType allowHO emb env (val $ txRefSort tcEnv emb t)

checkDupIntersect     :: [(Var, Located SpecType)] -> [(Var, Located SpecType)] -> [Error]
checkDupIntersect xts asmSigs = concatMap mkWrn {- trace msg -} dups
  where
    mkWrn (x, t)     = pprWrn x (sourcePosSrcSpan $ loc t)
    dups             = L.intersectBy ((==) `on` fst) asmSigs xts
    pprWrn v l       = trace ("WARNING: Assume Overwrites Specifications for "++ show v ++ " : " ++ showPpr l) []
    -- msg              = "CHECKDUPINTERSECT:" ++ msg1 ++ msg2
    -- msg1             = "\nCheckd-SIGS:\n" ++ showpp (M.fromList xts)
    -- msg2             = "\nAssume-SIGS:\n" ++ showpp (M.fromList asmSigs)

checkDuplicate        :: [(Var, Located SpecType)] -> [Error]
checkDuplicate xts = mkErr <$> dups
  where
    mkErr (x, ts) = ErrDupSpecs (getSrcSpan x) (pprint x) (sourcePosSrcSpan . loc <$> ts)
    dups          = [z | z@(_, _:_:_) <- M.toList $ group xts ]

checkDuplicateRTAlias :: String -> [RTAlias s a] -> [Error]
checkDuplicateRTAlias s tas = mkErr <$> dups
  where
    mkErr xs@(x:_)          = ErrDupAlias (sourcePosSrcSpan $ rtPos x)
                                          (text s)
                                          (pprint $ rtName x)
                                          (sourcePosSrcSpan . rtPos <$> xs)
    mkErr []                = panic Nothing "mkError: called on empty list"
    dups                    = [z | z@(_:_:_) <- L.groupBy ((==) `on` rtName) tas]


checkMismatch        :: (Var, Located SpecType) -> Maybe Error
checkMismatch (x, t) = if ok then Nothing else Just err
  where
    ok               = tyCompat x (val t)
    err              = errTypeMismatch x t

tyCompat :: Var -> RType RTyCon RTyVar r -> Bool
tyCompat x t         = lhs == rhs
  where
    lhs :: RSort     = toRSort t
    rhs :: RSort     = ofType $ varType x

errTypeMismatch     :: Var -> Located SpecType -> Error
errTypeMismatch x t = ErrMismatch lqSp (pprint x) d1 d2 hsSp
  where
    d1              = pprint $ varType x
    d2              = pprint $ toType $ val t
    lqSp            = sourcePosSrcSpan $ loc t
    hsSp            = getSrcSpan x

------------------------------------------------------------------------------------------------
-- | @checkRType@ determines if a type is malformed in a given environment ---------------------
------------------------------------------------------------------------------------------------
checkRType :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r) => Bool -> TCEmb TyCon -> SEnv SortedReft -> RRType (UReft r) -> Maybe Doc
------------------------------------------------------------------------------------------------

checkRType allowHO emb env t
  =   checkAppTys t
  <|> checkAbstractRefs t
  <|> efoldReft farg cb (tyToBind emb) (rTypeSortedReft emb) f insertPEnv env Nothing t
  where
    cb c ts            = classBinds (rRCls c ts)
    farg _ t           = allowHO || isBase t  -- this check should be the same as the one in addCGEnv
    f env me r err     = err <|> checkReft env emb me r
    insertPEnv p γ     = insertsSEnv γ (mapSnd (rTypeSortedReft emb) <$> pbinds p)
    pbinds p           = (pname p, pvarRType p :: RSort) : [(x, tx) | (tx, x, _) <- pargs p]

tyToBind :: TCEmb TyCon -> RTVar RTyVar RSort  -> [(Symbol, SortedReft)]
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
        foldl (\merr t -> merr <|> go t) Nothing ts
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
    expectedArity = realTcArity tc

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
  :: (PPrint t, Reftable t, SubsTy RTyVar RSort t) =>
     RType RTyCon RTyVar (UReft t) -> Maybe Doc
checkAbstractRefs t = go t
  where
    penv = mkPEnv t

    go (RAllT _ t)        = go t
    go (RAllP _ t)        = go t
    go (RAllS _ t)        = go t
    go t@(RApp c ts rs r) = check (toRSort t :: RSort) r <|>  efold go ts <|> go' c rs
    go t@(RFun _ t1 t2 r) = check (toRSort t :: RSort) r <|> go t1 <|> go t2
    go t@(RVar _ r)       = check (toRSort t :: RSort) r
    go (RAllE _ t1 t2)    = go t1 <|> go t2
    go (REx _ t1 t2)      = go t1 <|> go t2
    go t@(RAppTy t1 t2 r) = check (toRSort t :: RSort) r <|> go t1 <|> go t2
    go (RRTy xts _ _ t)   = efold go (snd <$> xts) <|> go t
    go (RExprArg _)       = Nothing
    go (RHole _)          = Nothing

    go' c rs = foldl (\acc (x, y) -> acc <|> checkOne' x y) Nothing (zip rs (rTyConPVs c))

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


    efold f = foldl (\acc x -> acc <|> f x) Nothing

    check s (MkUReft _ (Pr ps) _) = foldl (\acc pp -> acc <|> checkOne s pp) Nothing ps

    checkOne s p | pvType' p /= s
                 = Just $ text "Incorrect Sort:\n\t"
                       <+> text "Abstract refinement with type"
                       <+> pprint (pvType' p)
                       <+> text "is applied to"
                       <+> pprint s
                       <+> text "\n\t In" <+> pprint p
                 | or [x == y | (_, x, EVar y) <- pargs p]
                 = Just $ text "Missing arguments on " <+> pprint p
                 | otherwise
                 = Nothing

    mkPEnv (RAllT _ t) = mkPEnv t
    mkPEnv (RAllP p t) = p:mkPEnv t
    mkPEnv _           = []

    pvType' p = safeHead (showpp p ++ " not in env of " ++ showpp t) [pvType q | q <- penv, pname p == pname q]




checkReft                    :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r) => SEnv SortedReft -> TCEmb TyCon -> Maybe (RRType (UReft r)) -> UReft r -> Maybe Doc
checkReft _   _   Nothing _  = Nothing -- TODO:RPropP/Ref case, not sure how to check these yet.
checkReft env emb (Just t) _ = (dr $+$) <$> checkSortedReftFull env' r
  where
    r                        = rTypeSortedReft emb t
    dr                       = text "Sort Error in Refinement:" <+> pprint r
    env'                     = foldl (\e (x, s) -> insertSEnv x (RR s mempty) e) env wiredSortedSyms

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
checkMeasures :: M.HashMap TyCon FTycon -> SEnv SortedReft -> [Measure SpecType DataCon] -> [Error]
---------------------------------------------------------------------------------------------------
checkMeasures emb env = concatMap (checkMeasure emb env)

checkMeasure :: M.HashMap TyCon FTycon -> SEnv SortedReft -> Measure SpecType DataCon -> [Error]
checkMeasure emb γ (M name@(Loc src _ n) sort body)
  = [txerror e | Just e <- checkMBody γ emb name sort <$> body]
  where
    txerror = ErrMeas (sourcePosSrcSpan src) (pprint n)

checkMBody :: (PPrint r,Reftable r,SubsTy RTyVar RSort r)
           => SEnv SortedReft
           -> TCEmb TyCon
           -> t
           -> SpecType
           -> Def (RRType r) DataCon
           -> Maybe Doc
checkMBody γ emb _ sort (Def _ as c _ bs body) = checkMBody' emb sort' γ' body
  where
    γ'    = L.foldl' (\γ (x, t) -> insertSEnv x t γ) γ (ats ++ xts)
    ats   = mapSnd (rTypeSortedReft emb) <$> as
    xts   = zip (fst <$> bs) $ rTypeSortedReft emb . subsTyVars_meet su <$> ty_args trep
    trep  = toRTypeRep ct
    su    = checkMBodyUnify (ty_res trep) (last txs)
    txs   = snd4 $ bkArrowDeep sort
    ct    = ofType $ dataConUserType c :: SpecType
    sort' = dropNArgs (length as) sort

checkMBodyUnify
  :: RType t t2 t1 -> RType c tv r -> [(t2,RType c tv (),RType c tv r)]
checkMBodyUnify                 = go
  where
    go (RVar tv _) t            = [(tv, toRSort t, t)]
    go t@(RApp {}) t'@(RApp {}) = concat $ zipWith go (rt_args t) (rt_args t')
    go _ _                      = []

checkMBody' :: (PPrint r,Reftable r,SubsTy RTyVar RSort r)
            => TCEmb TyCon
            -> RType RTyCon RTyVar r
            -> SEnv SortedReft
            -> Body
            -> Maybe Doc
checkMBody' emb sort γ body = case body of
    E e   -> checkSortFull γ (rTypeSort emb sort') e
    P p   -> checkSortFull γ boolSort  p
    R s p -> checkSortFull (insertSEnv s sty γ) boolSort p
  where
    -- psort = FApp propFTyCon []
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
  byName = L.groupBy ((==) `on` (val.name)) ms

  byTyCon = concatMap (L.groupBy ((==) `on` (dataConTyCon . ctor . head . eqns)))
                      byName

  checkOne []     = impossible Nothing "checkClassMeasures.checkOne on empty measure group"
  checkOne [_]    = Nothing
  checkOne (m:ms) = Just (ErrDupMeas (sourcePosSrcSpan (loc (name m)))
                                     (pprint (val (name m)))
                                     (pprint ((dataConTyCon . ctor . head . eqns) m))
                                     (map (sourcePosSrcSpan.loc.name) (m:ms)))
