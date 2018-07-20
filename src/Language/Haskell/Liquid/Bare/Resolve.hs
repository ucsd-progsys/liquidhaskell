-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc. 

{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PartialTypeSignatures #-}

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
  , ofBareExpr
  ) where 

import qualified Data.Maybe                        as Mb
import qualified Data.HashMap.Strict               as M
import qualified Text.PrettyPrint.HughesPJ         as PJ 

import qualified ConLike                           as Ghc
import qualified Var                               as Ghc
import qualified Module                            as Ghc
import qualified GHC                               as Ghc
import qualified DataCon                           as Ghc

import qualified Language.Fixpoint.Types           as F 
import qualified Language.Fixpoint.Misc            as Misc 
import           Language.Haskell.Liquid.Types   
import qualified Language.Haskell.Liquid.GHC.Misc  as GM 
import qualified Language.Haskell.Liquid.Measure   as Ms
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

resolveWith :: (Ghc.TyThing -> Maybe a) -> _ -> _ -> _ -> LocSymbol 
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
  resolveLocSym env name kind lx = case resolveLocSym env name "Var" lx of 
    Left e               -> Right (val lx)
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

-------------------------------------------------------------------------------
-- MOVE INTO RESOLVE 
-------------------------------------------------------------------------------

ofBareType :: Env -> ModName -> Located BareType -> Located SpecType 
ofBareType = undefined  

ofBareExpr :: Env -> ModName -> Located F.Expr -> Located F.Expr 
ofBareExpr = undefined 

