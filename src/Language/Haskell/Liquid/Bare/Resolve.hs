-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc. 

{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ConstraintKinds       #-}

module Language.Haskell.Liquid.Bare.Resolve 
  ( -- * Creating the Environment
    makeEnv 

    -- * Resolving symbols 
  , ResolveSym (..)
  , strictResolveSym 

  , Qualify (..)

    -- * Resolving types etc. 
  , Resolvable (..)

  -- * Misc 
  , resolveNamedVar 

  -- * Conversions from Bare
  , ofBareType
  -- , ofBareExpr
  ) where 

import qualified Data.Maybe                        as Mb
import qualified Data.HashMap.Strict               as M
import qualified Text.PrettyPrint.HughesPJ         as PJ 

import qualified ConLike                           as Ghc
import qualified Var                               as Ghc
-- import qualified Module                            as Ghc
import qualified GHC                               as Ghc
import qualified DataCon                           as Ghc
import qualified TysWiredIn                        as Ghc 
import qualified BasicTypes                        as Ghc 
import qualified Type                              as Ghc 
import qualified TyCon                             as Ghc 
import qualified Name                              as Ghc

-- import BasicTypes
-- import Type (expandTypeSynonyms)
-- import TysWiredIn





import qualified Language.Fixpoint.Types               as F 
import qualified Language.Fixpoint.Misc                as Misc 
import           Language.Haskell.Liquid.Types   
import qualified Language.Haskell.Liquid.GHC.Misc      as GM 
import qualified Language.Haskell.Liquid.Measure       as Ms
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Bare.Types 
import           Language.Haskell.Liquid.Bare.Misc   

-------------------------------------------------------------------------------
-- | Qualify various names 
-------------------------------------------------------------------------------
class Qualify a where 
  qualify :: Env -> ModName -> a -> a 

instance Qualify F.Equation where 
  qualify _env _name x = x -- TODO-REBARE 
-- REBARE: qualifyAxiomEq :: Bare.Env -> Var -> Subst -> AxiomEq -> AxiomEq
-- REBARE: qualifyAxiomEq v su eq = subst su eq { eqName = symbol v}

instance Qualify F.Symbol where 
  qualify env name x = case resolveSym env name "Symbol" x of 
    Left  _   -> x 
    Right val -> val 
-- REBARE: qualifySymbol :: Env -> F.Symbol -> F.Symbol
-- REBARE: qualifySymbol env x = maybe x F.symbol (M.lookup x syms)

instance Qualify LocSpecType where 
  qualify env _ lx = F.subst (_reSubst env) <$> lx 

instance Qualify F.Expr where 
  qualify env _ e = F.subst (_reSubst env) e 

instance Qualify LocSymbol where 
  qualify env name lx = qualify env name <$> lx 

instance Qualify SizeFun where 
  qualify env name (SymSizeFun lx) = SymSizeFun (qualify env name lx)
  qualify _   _    sf              = sf

instance Qualify TyConInfo where 
  qualify env name tci = tci { sizeFunction = qualify env name <$> sizeFunction tci }

instance Qualify RTyCon where 
  qualify env name rtc = rtc { rtc_info = qualify env name $ rtc_info rtc }

-------------------------------------------------------------------------------
-- | Creating an environment 
-------------------------------------------------------------------------------
makeEnv :: GhcSrc -> [(ModName, Ms.BareSpec)] -> LogicMap -> Env 
makeEnv src specs lmap = RE 
  { reLMap      = lmap
  , reSyms      = syms 
  , reSpecs     = specs 
  , _reSubst    = F.mkSubst [ (x, mkVarExpr v) | (x, v) <- syms ]
  , _reTyThings = makeTyThingMap src 
  } 
  where 
    syms     = [ (F.symbol v, v) | v <- vars ] 
    vars     = srcVars src

makeTyThingMap :: GhcSrc -> TyThingMap 
makeTyThingMap src = Misc.group [ (x, (m, t)) | t         <- srcThings src
                                              , let (m, x) = thingNames t ] 
  where
    thingNames     = GM.splitModuleName . F.symbol

srcThings :: GhcSrc -> [Ghc.TyThing] 
srcThings src = [ Ghc.AnId   x | x <- vars ++ dcVars ] 
             ++ [ Ghc.ATyCon c | c <- tcs            ] 
             ++ [ aDataCon   d | d <- dcs            ] 
  where 
    dcVars    = dataConVars dcs 
    dcs       = concatMap Ghc.tyConDataCons tcs 
    tcs       = srcTyCons   src 
    vars      = srcVars     src
    aDataCon  = Ghc.AConLike . Ghc.RealDataCon 

srcTyCons :: GhcSrc -> [Ghc.TyCon]
srcTyCons src = concat 
  [ gsTcs   src 
  , gsFiTcs src 
  ]

srcVars :: GhcSrc -> [Ghc.Var]
srcVars src = concat 
  [ giDerVars src
  , giImpVars src 
  , giDefVars src 
  , giUseVars src 
  ]

dataConVars :: [Ghc.DataCon] -> [Ghc.Var]
dataConVars dcs = concat 
  [ Ghc.dataConWorkId <$> dcs 
  , Ghc.dataConWrapId <$> dcs 
  ] 

lookupTyThing :: Env -> ModName -> F.Symbol -> [Ghc.TyThing]
lookupTyThing env name sym = [ t | (m, t) <- M.lookupDefault [] x (_reTyThings env), m == mod ] 
  where 
    (mod, x)               = unQualifySymbol name sym
 
-- | `unQualifySymbol name sym` splits `sym` into a pair `(mod, rest)` where 
--   `mod` is the name of the module (derived from `sym` if qualified or from `name` otherwise).

unQualifySymbol :: ModName -> F.Symbol -> (F.Symbol, F.Symbol)
unQualifySymbol name sym 
  | GM.isQualifiedSym sym = GM.splitModuleName sym 
  | otherwise             = (F.symbol name, sym)

-- srcDataCons :: GhcSrc -> [Ghc.DataCon]
-- srcDataCons src = concatMap Ghc.tyConDataCons (srcTyCons src) 

{- 
  let expSyms     = S.toList (exportedSymbols mySpec)
  syms0 <- liftedVarMap (varInModule name) expSyms
  syms1 <- symbolVarMap (varInModule name) vars (S.toList $ importedSymbols name   specs)
  syms2    <- symbolVarMap (varInModule name) (vars ++ map fst cs') fSyms
  let fSyms =  freeSymbols xs' (sigs ++ asms ++ cs') ms' ((snd <$> invs) ++ (snd <$> ialias))
            ++ measureSymbols measures
   * Symbol :-> [(ModuleName, TyCon)]
   * Symbol :-> [(ModuleName, Var  )]
   * 
 -}
 
instance F.Symbolic Ghc.TyThing where 
  symbol = tyThingSymbol 

tyThingSymbol :: Ghc.TyThing -> F.Symbol 
tyThingSymbol (Ghc.AnId     x) = F.symbol x
tyThingSymbol (Ghc.ATyCon   c) = F.symbol c
tyThingSymbol (Ghc.AConLike d) = conLikeSymbol d 
tyThingSymbol (_)              = panic Nothing "TODO: tyThingSymbol" 

conLikeSymbol :: Ghc.ConLike -> F.Symbol 
conLikeSymbol (Ghc.RealDataCon d) = F.symbol d 
conLikeSymbol _                   = panic Nothing "TODO: conLikeSymbol"
-------------------------------------------------------------------------------
resolveNamedVar :: (Ghc.NamedThing a, F.Symbolic a) => Env -> ModName -> a -> Ghc.Var
-------------------------------------------------------------------------------
resolveNamedVar env name z = strictResolveSym env name "Var" lx 
  where 
    lx                     = GM.namedLocSymbol z

-------------------------------------------------------------------------------
-- | Using the environment 
-------------------------------------------------------------------------------
class ResolveSym a where 
  resolveLocSym :: Env -> ModName -> String -> LocSymbol -> Either UserError a 
  
instance ResolveSym Ghc.Var where 
  resolveLocSym = resolveWith $ \case {Ghc.AnId x -> Just x; _ -> Nothing}

instance ResolveSym Ghc.TyCon where 
  resolveLocSym = resolveWith $ \case {Ghc.ATyCon x -> Just x; _ -> Nothing}

resolveWith :: (Ghc.TyThing -> Maybe a) -> Env -> ModName -> String -> LocSymbol 
            -> Either UserError a 
resolveWith f env name kind lx = 
  case Mb.mapMaybe f things of 
    []  -> Left  (errResolve kind lx) 
    x:_ -> Right x 
  where 
    things         = lookupTyThing env name (val lx) 
      
errResolve :: String -> LocSymbol -> UserError 
errResolve kind lx = ErrResolve (GM.fSrcSpan lx) (PJ.text msg)
  where 
    msg            = unwords [ "Name resolution error: ", kind, symbolicIdent lx]

symbolicIdent :: (F.Symbolic a) => a -> String
symbolicIdent x = "'" ++ symbolicString x ++ "'"

symbolicString :: F.Symbolic a => a -> String
symbolicString = F.symbolString . F.symbol

instance ResolveSym F.Symbol where 
  resolveLocSym env name _ lx = case resolveLocSym env name "Var" lx of 
    Left _               -> Right (val lx)
    Right (v :: Ghc.Var) -> Right (F.symbol v)

resolveSym :: (ResolveSym a) => Env -> ModName -> String -> F.Symbol -> Either UserError a 
resolveSym env name kind x = resolveLocSym env name kind (F.dummyLoc x) 

-- | @strictResolve@ wraps the plain @resolve@ to throw an error 
--   if the name being searched for is unknown.
strictResolveSym :: (ResolveSym a) => Env -> ModName -> String -> LocSymbol -> a 
strictResolveSym env name kind x = case resolveLocSym env name kind x of 
  Left  err -> uError err 
  Right val -> val 

class Resolvable a where 
  resolve :: Env -> ModName -> F.SourcePos -> a -> a  

instance Resolvable F.Qualifier where 
  resolve _ _ _ q = q -- TODO-REBARE 

instance Resolvable RReft where 
  resolve _ _ _ r = r -- TODO-REBARE 

instance Resolvable F.Expr where 
  resolve _ _ _ e = e -- TODO-REBARE 
  
instance Resolvable a => Resolvable (Located a) where 
  resolve env name _ lx = F.atLoc lx (resolve env name (F.loc lx) (val lx))

-------------------------------------------------------------------------------
-- | HERE 
-------------------------------------------------------------------------------
ofBareType :: Env -> ModName -> F.SourcePos -> BareType -> SpecType 
ofBareType env name l t = ofBRType env name (resolve env name l) l t 

ofBSort :: Env -> ModName -> F.SourcePos -> BSort -> RSort 
ofBSort env name l t = ofBRType env name id l t 

ofBPVar :: Env -> ModName -> F.SourcePos -> BPVar -> RPVar
ofBPVar env name l = fmap (ofBSort env name l) 
--------------------------------------------------------------------------------
type Expandable r = ( PPrint r
                    , F.Reftable r
                    , SubsTy RTyVar (RType RTyCon RTyVar ()) r
                    , F.Reftable (RTProp RTyCon RTyVar r))

ofBRType :: (Expandable r) => Env -> ModName -> (r -> r) -> F.SourcePos -> BRType r 
         -> RRType r 
ofBRType env name f l t  = go t 
  where
    goReft r             = f r 
    go (RAppTy t1 t2 r)  = RAppTy (go t1) (go t2) (goReft r)
    go (RApp tc ts rs r) = goRApp tc ts rs r 
    go (RImpF x t1 t2 r) = goRImpF x t1 t2 r 
    go (RFun  x t1 t2 r) = goRFun  x t1 t2 r 
    go (RVar a r)        = RVar (RT.bareRTyVar a)   (goReft r)
    go (RAllT a t)       = RAllT a' (go t) 
      where a'           = dropTyVarInfo (mapTyVarValue RT.bareRTyVar a) 
    go (RAllP a t)       = RAllP a' (go t) 
      where a'           = ofBPVar env name l a 
    go (RAllS x t)       = RAllS x (go t)
    go (RAllE x t1 t2)   = RAllE x (go t1) (go t2)
    go (REx x t1 t2)     = REx   x (go t1) (go t2)
    go (RRTy e r o t)    = RRTy  e'  (goReft r) o (go t)
      where e'           = Misc.mapSnd go <$> e
    go (RHole r)         = RHole (goReft r) 
    go (RExprArg le)     = RExprArg (resolve env name (F.loc le) le) 
    goRef (RProp ss (RHole r)) = rPropP (goSyms <$> ss) (goReft r)
    goRef (RProp ss t)         = RProp  (goSyms <$> ss) (go t)
    goSyms (x, t)              = (x, ofBSort env name l t) 
    goRImpF x t1 t2 r          = RImpF x (rebind x (go t1)) (go t2) (goReft r)
    goRFun x t1 t2 r           = RFun x (rebind x (go t1)) (go t2) (goReft r)
    goRApp tc ts rs r          = bareTCApp (goReft r) lc' (goRef <$> rs) (go <$> ts)
      where
        lc'                    = F.atLoc lc (matchTyCon env name lc (length ts))
        lc                     = btc_tc tc
    -- goRApp _ _ _ _             = impossible Nothing "goRApp failed through to final case"
    rebind x t                 = F.subst1 t (x, F.EVar $ rTypeValueVar t)

    -- TODO-REBARE: goRImpF bounds _ (RApp c ps' _ _) t _
    -- TODO-REBARE:  | Just bnd <- M.lookup (btc_tc c) bounds
    -- TODO-REBARE:   = do let (ts', ps) = splitAt (length $ tyvars bnd) ps'
    -- TODO-REBARE:        ts <- mapM go ts'
    -- TODO-REBARE:        makeBound bnd ts [x | RVar (BTV x) _ <- ps] <$> go t
    -- TODO-REBARE: goRFun bounds _ (RApp c ps' _ _) t _
    -- TODO-REBARE: | Just bnd <- M.lookup (btc_tc c) bounds
    -- TODO-REBARE: = do let (ts', ps) = splitAt (length $ tyvars bnd) ps'
    -- TODO-REBARE: ts <- mapM go ts'
    -- TODO-REBARE: makeBound bnd ts [x | RVar (BTV x) _ <- ps] <$> go t

  -- TODO-REBARE: ofBareRApp env name t@(F.Loc _ _ !(RApp tc ts _ r))
  -- TODO-REBARE: | Loc l _ c <- btc_tc tc
  -- TODO-REBARE: , Just rta <- M.lookup c aliases
  -- TODO-REBARE: = appRTAlias l rta ts =<< resolveReft r

matchTyCon :: Env -> ModName -> LocSymbol -> Int -> Ghc.TyCon
matchTyCon env name lc@(Loc _ _ c) arity
  | isList c && arity == 1  = Ghc.listTyCon
  | isTuple c               = Ghc.tupleTyCon Ghc.Boxed arity
  | otherwise               = strictResolveSym env name "matchTyCon" lc 

bareTCApp :: (Expandable r) 
          => r
          -> Located Ghc.TyCon
          -> [RTProp RTyCon RTyVar r]
          -> [RType RTyCon RTyVar r]
          -> (RType RTyCon RTyVar r)
bareTCApp r (Loc l _ c) rs ts | Just rhs <- Ghc.synTyConRhs_maybe c
  = if (GM.kindTCArity c < length ts) 
      then uError err
      else tyApp (RT.subsTyVars_meet su $ RT.ofType rhs) (drop nts ts) rs r
    where
       tvs = [ v | (v, b) <- zip (GM.tyConTyVarsDef c) (Ghc.tyConBinders c), GM.isAnonBinder b]
       su  = zipWith (\a t -> (RT.rTyVar a, toRSort t, t)) tvs ts
       nts = length tvs

       err :: UserError
       err = ErrAliasApp (GM.sourcePosSrcSpan l) (pprint c) (Ghc.getSrcSpan c)
                         (PJ.hcat [ PJ.text "Expects"
                                  , pprint (GM.realTcArity c) 
                                  , PJ.text "arguments, but is given" 
                                  , pprint (length ts) ] )
-- TODO expandTypeSynonyms here to
bareTCApp r (Loc _ _ c) rs ts | Ghc.isFamilyTyCon c && isTrivial t
  = expandRTypeSynonyms (t `RT.strengthen` r)
  where t = RT.rApp c ts rs mempty

bareTCApp r (Loc _ _ c) rs ts
  = RT.rApp c ts rs r


tyApp :: F.Reftable r => RType c tv r -> [RType c tv r] -> [RTProp c tv r] -> r 
      -> RType c tv r
tyApp (RApp c ts rs r) ts' rs' r' = RApp c (ts ++ ts') (rs ++ rs') (r `F.meet` r')
tyApp t                []  []  r  = t `RT.strengthen` r
tyApp _                 _  _   _  = panic Nothing $ "Bare.Type.tyApp on invalid inputs"

expandRTypeSynonyms :: (Expandable r) => RRType r -> RRType r
expandRTypeSynonyms = RT.ofType . Ghc.expandTypeSynonyms . RT.toType
                   