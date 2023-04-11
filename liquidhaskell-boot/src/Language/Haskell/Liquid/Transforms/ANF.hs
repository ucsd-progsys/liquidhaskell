--------------------------------------------------------------------------------
-- | Convert GHC Core into Administrative Normal Form (ANF) --------------------
--------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ViewPatterns               #-}

module Language.Haskell.Liquid.Transforms.ANF (anormalize) where

import           Prelude                          hiding (error)
import           Liquid.GHC.TypeRep
import           Liquid.GHC.API  as Ghc hiding ( mkTyArg
                                                                , showPpr
                                                                , DsM
                                                                , panic)
import qualified Liquid.GHC.API  as Ghc
import           Control.Monad.State.Lazy
import           System.Console.CmdArgs.Verbosity (whenLoud)
import qualified Language.Fixpoint.Types    as F

import           Language.Haskell.Liquid.UX.Config  as UX
import qualified Language.Haskell.Liquid.Misc       as Misc
import           Liquid.GHC.Misc   as GM
import           Language.Haskell.Liquid.Transforms.Rec
import           Language.Haskell.Liquid.Transforms.InlineAux
import           Language.Haskell.Liquid.Transforms.Rewrite
import           Language.Haskell.Liquid.Types.Errors

import qualified Liquid.GHC.SpanStack as Sp
import qualified Liquid.GHC.Resugar   as Rs
import           Data.Maybe                       (fromMaybe)
import           Data.List                        (sortBy, (\\))
import qualified Text.Printf as Printf
import           Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

--------------------------------------------------------------------------------
-- | A-Normalize a module ------------------------------------------------------
--------------------------------------------------------------------------------
anormalize :: UX.Config -> HscEnv -> ModGuts -> IO [CoreBind]
--------------------------------------------------------------------------------
anormalize cfg hscEnv modGuts = do
  whenLoud $ do
    putStrLn "***************************** GHC CoreBinds ***************************"
    putStrLn $ GM.showCBs untidy (mg_binds modGuts)
    putStrLn "***************************** REC CoreBinds ***************************"
    putStrLn $ GM.showCBs untidy orig_cbs
    putStrLn "***************************** RWR CoreBinds ***************************"
    putStrLn $ GM.showCBs untidy rwr_cbs
  fromMaybe err . snd <$> initDsWithModGuts hscEnv modGuts act -- hscEnv m grEnv tEnv emptyFamInstEnv act
    where
      err      = panic Nothing "Oops, cannot A-Normalize GHC Core!"
      act      = Misc.concatMapM (normalizeTopBind γ0) rwr_cbs
      γ0       = emptyAnfEnv cfg
      rwr_cbs  = rewriteBinds cfg orig_cbs
      orig_cbs = transformRecExpr inl_cbs
      inl_cbs  = inlineAux cfg (mg_module modGuts) $ mg_binds modGuts
      untidy   = UX.untidyCore cfg

{-
      m        = mgi_module modGuts
      grEnv    = mgi_rdr_env modGuts
      tEnv     = modGutsTypeEnv modGuts

modGutsTypeEnv :: MGIModGuts -> TypeEnv
modGutsTypeEnv mg  = typeEnvFromEntities ids tcs fis
  where
    ids            = bindersOfBinds (mgi_binds mg)
    tcs            = mgi_tcs mg
    fis            = mgi_fam_insts mg
-}

--------------------------------------------------------------------------------
-- | A-Normalize a @CoreBind@ --------------------------------------------------
--------------------------------------------------------------------------------

-- Can't make the below default for normalizeBind as it
-- fails tests/pos/lets.hs due to GHCs odd let-bindings

normalizeTopBind :: AnfEnv -> Bind CoreBndr -> Ghc.DsM [CoreBind]
normalizeTopBind γ (NonRec x e)
  = do e' <- runDsM $ evalStateT (stitch γ e) (DsST [])
       return [normalizeTyVars $ NonRec x e']

normalizeTopBind γ (Rec xes)
  = do xes' <- runDsM $ execStateT (normalizeBind γ (Rec xes)) (DsST [])
       return $ map normalizeTyVars (st_binds xes')

normalizeTyVars :: Bind Id -> Bind Id
normalizeTyVars (NonRec x e) = NonRec (setVarType x t') $ normalizeForAllTys e
  where
    t'       = subst msg as as' bt
    msg      = "WARNING: unable to renameVars on " ++ GM.showPpr x
    as'      = fst $ splitForAllTyCoVars $ exprType e
    (as, bt) = splitForAllTyCoVars (varType x)
normalizeTyVars (Rec xes)    = Rec xes'
  where
    nrec     = normalizeTyVars <$> (uncurry NonRec <$> xes)
    xes'     = (\case NonRec x e -> (x, e); _ -> impossible Nothing "This cannot happen") <$> nrec

subst :: String -> [TyVar] -> [TyVar] -> Type -> Type
subst msg as as' bt
  | length as == length as'
  = mkForAllTys (mkTyArg <$> as') $ substTy su bt
  | otherwise
  = trace msg $ mkForAllTys (mkTyArg <$> as) bt
  where su = mkTvSubstPrs $ zip as (mkTyVarTys as')

-- | eta-expand CoreBinds with quantified types
normalizeForAllTys :: CoreExpr -> CoreExpr
normalizeForAllTys e = case e of
  Lam b _ | isTyVar b
    -> e
  _ -> mkLams tvs (mkTyApps e (map mkTyVarTy tvs))
  where
  (tvs, _) = splitForAllTyCoVars (exprType e)


newtype DsM a = DsM {runDsM :: Ghc.DsM a}
   deriving (Functor, Monad, MonadUnique, Applicative)

newtype DsST = DsST { st_binds :: [CoreBind] }

type DsMW = StateT DsST DsM

------------------------------------------------------------------
normalizeBind :: AnfEnv -> CoreBind -> DsMW ()
------------------------------------------------------------------
normalizeBind γ (NonRec x e)
  = do e' <- normalize γ e
       add [NonRec x e']

normalizeBind γ (Rec xes)
  = do es' <- mapM (stitch γ) es
       add [Rec (zip xs es')]
    where
       (xs, es) = unzip xes

--------------------------------------------------------------------
normalizeName :: AnfEnv -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------

-- normalizeNameDebug γ e
--   = liftM (tracePpr ("normalizeName" ++ showPpr e)) $ normalizeName γ e

normalizeName γ e@(Lit l)
  | shouldNormalize l
  = normalizeLiteral γ e
  | otherwise
  = return e

normalizeName γ (Var x)
  = return $ Var (lookupAnfEnv γ x x)

normalizeName _ e@(Type _)
  = return e

normalizeName γ e@(Coercion _)
  = do x     <- lift $ freshNormalVar γ $ exprType e
       add  [NonRec x e]
       return $ Var x

normalizeName γ (Tick tt e)
  = do e'    <- normalizeName (γ `at` tt) e
       return $ Tick tt e'

normalizeName γ e
  = do e'   <- normalize γ e
       x    <- lift $ freshNormalVar γ $ exprType e
       add [NonRec x e']
       return $ Var x

shouldNormalize :: Literal -> Bool
shouldNormalize (LitNumber {})  = True
shouldNormalize (LitString {})    = True
shouldNormalize _               = False

add :: [CoreBind] -> DsMW ()
add w = modify $ \s -> s { st_binds = st_binds s ++ w}

--------------------------------------------------------------------------------
normalizeLiteral :: AnfEnv -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------------------
normalizeLiteral γ e =
  do x <- lift $ freshNormalVar γ $ exprType e
     add [NonRec x e]
     return $ Var x

--------------------------------------------------------------------------------
normalize :: AnfEnv -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------------------
normalize γ e
  | UX.patternFlag γ
  , Just p <- Rs.lift e
  = normalizePattern γ p

normalize γ (Lam x e) | isTyVar x
  = do e' <- normalize γ e
       return $ Lam x e'

normalize γ (Lam x e)
  = do e' <- stitch γ e
       return $ Lam x e'

normalize γ (Let b e)
  = do normalizeBind γ b
       normalize γ e
       -- Need to float bindings all the way up to the top
       -- Due to GHCs odd let-bindings (see tests/pos/lets.hs)

normalize γ (Case e x t as)
  = do n     <- normalizeName γ e
       x'    <- lift $ freshNormalVar γ τx -- rename "wild" to avoid shadowing
       let γ' = extendAnfEnv γ x x'
       as'   <- forM as $ \(Alt c xs e') -> fmap (Alt c xs) (stitch (incrCaseDepth c γ') e')
       as''  <- lift $ expandDefaultCase γ τx as'
       return $ Case n x' t as''
    where τx = GM.expandVarType x

normalize γ (Var x)
  = return $ Var (lookupAnfEnv γ x x)

normalize _ e@(Lit _)
  = return e

normalize _ e@(Type _)
  = return e

normalize γ (Cast e τ)
  = do e' <- normalizeName γ e
       return $ Cast e' τ

normalize γ (App e1 e2@(Type _))
  = do e1' <- normalize γ e1
       e2' <- normalize γ e2
       return $ App e1' e2'

normalize γ (App e1 e2)
  = do e1' <- normalize γ e1
       n2  <- normalizeName γ e2
       return $ App e1' n2

normalize γ (Tick tt e)
  = do e' <- normalize (γ `at` tt) e
       return $ Tick tt e'

normalize _ (Coercion c)
  = return $ Coercion c

--------------------------------------------------------------------------------
stitch :: AnfEnv -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------------------
stitch γ e
  = do bs'   <- get
       modify $ \s -> s { st_binds = [] }
       e'    <- normalize γ e
       bs    <- st_binds <$> get
       put bs'
       return $ mkCoreLets bs e'

_mkCoreLets' :: [CoreBind] -> CoreExpr -> CoreExpr
_mkCoreLets' bs e = mkCoreLets bs1 e1
  where
    (e1, bs1)    = GM.tracePpr "MKCORELETS" (e, bs)

--------------------------------------------------------------------------------
normalizePattern :: AnfEnv -> Rs.Pattern -> DsMW CoreExpr
--------------------------------------------------------------------------------
normalizePattern γ p@(Rs.PatBind {}) = do
  -- don't normalize the >>= itself, we have a special typing rule for it
  e1'   <- normalize γ (Rs.patE1 p)
  e2'   <- stitch    γ (Rs.patE2 p)
  return $ Rs.lower p { Rs.patE1 = e1', Rs.patE2 = e2' }

normalizePattern γ p@(Rs.PatReturn {}) = do
  e'    <- normalize γ (Rs.patE p)
  return $ Rs.lower p { Rs.patE = e' }

normalizePattern _ p@(Rs.PatProject {}) =
  return (Rs.lower p)

normalizePattern γ p@(Rs.PatSelfBind {}) = do
  normalize γ (Rs.patE p)

normalizePattern γ p@(Rs.PatSelfRecBind {}) = do
  e'    <- normalize γ (Rs.patE p)
  return $ Rs.lower p { Rs.patE = e' }


--------------------------------------------------------------------------------
expandDefault :: AnfEnv -> Bool
--------------------------------------------------------------------------------
expandDefault γ = aeCaseDepth γ <= maxCaseExpand γ

--------------------------------------------------------------------------------
expandDefaultCase :: AnfEnv
                  -> Type
                  -> [CoreAlt]
                  -> DsM [CoreAlt]
--------------------------------------------------------------------------------
expandDefaultCase γ tyapp zs@(Alt DEFAULT _ _ : _) | expandDefault γ
  = expandDefaultCase' γ tyapp zs

expandDefaultCase γ tyapp@(TyConApp tc _) z@(Alt DEFAULT _ _:dcs)
  = case tyConDataCons_maybe tc of
       Just ds -> do let ds' = ds \\ [ d | Alt (DataAlt d) _ _ <- dcs]
                     let n   = length ds'
                     if n == 1
                       then expandDefaultCase' γ tyapp z
                       else if maxCaseExpand γ /= 2
                            then return z
                            else return (trace (expandMessage False γ n) z)
       Nothing -> return z --

expandDefaultCase _ _ z
   = return z

expandDefaultCase'
  :: AnfEnv -> Type -> [CoreAlt] -> DsM [CoreAlt]
expandDefaultCase' γ t (Alt DEFAULT _ e : dcs)
  | Just dtss <- GM.defaultDataCons t ((\(Alt dc _ _) -> dc) <$> dcs) = do
      dcs'    <- warnCaseExpand γ <$> forM dtss (cloneCase γ e)
      return   $ sortCases (dcs' ++ dcs)
expandDefaultCase' _ _ z
   = return z

cloneCase :: AnfEnv -> CoreExpr -> (DataCon, [TyVar], [Type]) -> DsM CoreAlt
cloneCase γ e (d, as, ts) = do
  xs  <- mapM (freshNormalVar γ) ts
  return (Alt (DataAlt d) (as ++ xs) e)

sortCases :: [CoreAlt] -> [CoreAlt]
sortCases = sortBy Ghc.cmpAlt

warnCaseExpand :: AnfEnv -> [a] -> [a]
warnCaseExpand γ xs
  | 10 < n          = trace (expandMessage True γ n) xs
  | otherwise       = xs
  where
   n                = length xs

expandMessage :: Bool -> AnfEnv -> Int -> String
expandMessage expand γ n = unlines [msg1, msg2]
  where
    msg1            = Printf.printf "WARNING: (%s) %s DEFAULT with %d cases at depth %d" (showPpr sp) v1 n d
    msg2            = Printf.printf "%s expansion with --max-case-expand=%d" v2 d'
    (v1, v2, d')
      | expand      = ("Expanding"    , "Disable", d-1) :: (String, String, Int)
      | otherwise   = ("Not expanding", "Enable" , d+1)
    d               = aeCaseDepth γ
    sp              = Sp.srcSpan (aeSrcSpan γ)

--------------------------------------------------------------------------------
-- | ANF Environments ----------------------------------------------------------
--------------------------------------------------------------------------------
freshNormalVar :: AnfEnv -> Type -> DsM Id
freshNormalVar γ t = do
  u     <- getUniqueM
  let i  = getKey u
  let sp = Sp.srcSpan (aeSrcSpan γ)
  return (mkUserLocal (anfOcc i) u Ghc.Many t sp)

anfOcc :: Int -> OccName
anfOcc = mkVarOccFS . GM.symbolFastString . F.intSymbol F.anfPrefix

data AnfEnv = AnfEnv
  { aeVarEnv    :: HashMap StableId Id
  -- ^ A mapping between a 'StableId' (see below) and an 'Id'.
  , aeSrcSpan   :: Sp.SpanStack
  , aeCfg       :: UX.Config
  , aeCaseDepth :: !Int
  }

-- | A \"stable\" 'Id'. When transforming 'Core' into ANF notation, we need to keep around a mapping between
-- a particular 'Var' (typically an 'Id') and an 'Id'. Previously this was accomplished using a 'VarEnv',
-- a GHC data structure where keys are 'Unique's. Working with 'Unique' in GHC is not always robust enough
-- when it comes to LH. First of all, the /way/ 'Unique's are constructed might change between GHC versions,
-- and they are not stable between rebuilds/compilations. In the case of this module, in GHC 9 the test
-- BST.hs was failing because two different 'Id's, namely \"wild_X2\" and \"dOrd_X2\" were being given the
-- same 'Unique' by GHC (i.e. \"X2\") which was causing the relevant entry to be overwritten in the 'AnfEnv'
-- causing a unification error.
--
-- A 'StableId' is simply a wrapper over an 'Id' with a different 'Eq' instance that really guarantee
-- uniqueness (for our purposes, anyway).
newtype StableId = StableId Id

instance Eq StableId where
  (StableId id1) == (StableId id2) =
    -- We first use the default 'Eq' instance, which works on uniques (basically, integers) and is
    -- efficient. If we get 'False' it means those 'Unique' are really different, but if we get 'True',
    -- we need to be /really/ sure that's the case by using the 'stableNameCmp' function on the 'Name's.
    -- Nothing to do when id1 == id2 as the uniques are /really/ different.
    (id1 == id2) && (stableNameCmp (getName id1) (getName id2) == EQ) -- Avoid unique clashing.

-- For the 'Hashable' instance, we rely on the 'Unique'. This means in pratice there is a tiny chance
-- of collision, but this should only marginally affects the efficiency of the data structure.
instance Hashable StableId where
  hashWithSalt s (StableId id1) = hashWithSalt s (getKey $ getUnique id1)

-- Shows this 'StableId' by also outputting the associated unique.
instance Show StableId where
  show (StableId id1) = nameStableString (getName id1) <> "_" <> show (getUnique id1)

instance UX.HasConfig AnfEnv where
  getConfig = aeCfg

emptyAnfEnv :: UX.Config -> AnfEnv
emptyAnfEnv cfg = AnfEnv
  { aeVarEnv    = mempty
  , aeSrcSpan   = Sp.empty
  , aeCfg       = cfg
  , aeCaseDepth = 1
  }

lookupAnfEnv :: AnfEnv -> Id -> Id -> Id
lookupAnfEnv γ x (StableId -> y) = HM.lookupDefault x y (aeVarEnv γ)

extendAnfEnv :: AnfEnv -> Id -> Id -> AnfEnv
extendAnfEnv γ (StableId -> x) y = γ { aeVarEnv = HM.insert x y (aeVarEnv γ) }

incrCaseDepth :: AltCon -> AnfEnv -> AnfEnv
incrCaseDepth DEFAULT γ = γ { aeCaseDepth = 1 + aeCaseDepth γ }
incrCaseDepth _       γ = γ

at :: AnfEnv -> CoreTickish -> AnfEnv
at γ tt = γ { aeSrcSpan = Sp.push (Sp.Tick tt) (aeSrcSpan γ)}
