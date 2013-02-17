module Language.Haskell.Liquid.Measure (  
    Spec (..)
  , MSpec (..)
  , Measure (name, sort)
  , Def (..)
  , Body (..)
  , mkM, mkMSpec
  , qualifySpec
  , mapTy
  , dataConTypes
  , expandRTAliases
  ) where

import GHC
import Var
import qualified Outputable as O 
import Text.PrettyPrint.HughesPJ hiding (first)

import DataCon
import qualified Data.HashMap.Strict as M 
-- import Data.Data
import Data.Monoid hiding ((<>))
import Data.List (foldl1')
import Data.Either (partitionEithers)
import Data.Bifunctor
import Control.Applicative      ((<$>))
import Control.Exception        (assert)

import Language.Fixpoint.Misc
import Language.Fixpoint.Types          hiding (name, body)
import Language.Haskell.Liquid.RefType

data Spec ty bndr  = Spec { 
    measures   :: ![Measure ty bndr]         -- ^ User-defined properties for ADTs
  , sigs       :: ![(Symbol, ty)]            -- ^ Imported functions and types   
  , invariants :: ![ty]                      -- ^ Data type invariants  
  , imports    :: ![Symbol]                  -- ^ Loaded spec module names
  , dataDecls  :: ![DataDecl]                -- ^ Predicated data definitions 
  , includes   :: ![FilePath]                -- ^ Included qualifier files
  , aliases    :: ![RTAlias String BareType] -- ^ RefType aliases
  , paliases   :: ![RTAlias Symbol Pred]     -- ^ Refinement/Predicate aliases
  , embeds     :: !(TCEmb String)            -- ^ GHC-Tycon-to-fixpoint Tycon map
  } 


data MSpec ty bndr = MSpec { 
    ctorMap :: M.HashMap Symbol [Def bndr]
  , measMap :: M.HashMap Symbol (Measure ty bndr) 
  }

data Measure ty bndr = M { 
    name :: Symbol
  , sort :: ty
  , eqns :: [Def bndr]
  } -- deriving (Data, Typeable)

data Def bndr 
  = Def { 
    measure :: Symbol
  , ctor    :: bndr
  , binds   :: [Symbol]
  , body    :: Body
  } deriving (Show)

data Body 
  = E Expr          -- ^ Measure Refinement: {v | v = e } 
  | P Pred          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Pred   -- ^ Measure Refinement: {v | p}
  deriving (Show)

qualifySpec name sp = sp { sigs = [ (qualifySymbol name x, t) | (x, t) <- sigs sp] }


mkM :: Symbol -> ty -> [Def bndr] -> Measure ty bndr
mkM name typ eqns 
  | all ((name ==) . measure) eqns
  = M name typ eqns
  | otherwise
  = errorstar $ "invalid measure definition for " ++ (show name)

mkMSpec ::  [Measure ty Symbol] -> MSpec ty Symbol
mkMSpec ms = MSpec cm mm 
  where cm  = groupMap ctor $ concatMap eqns ms'
        mm  = M.fromList [(name m, m) | m <- ms' ]
        ms' = checkFail "Duplicate Measure Definition" (distinct . fmap name) ms

instance Monoid (Spec ty bndr) where
  mappend (Spec xs ys invs zs ds is as ps es) (Spec xs' ys' invs' zs' ds' is' as' ps' es')
           = Spec (xs ++ xs') 
                  (ys ++ ys') 
                  (invs ++ invs') 
                  (sortNub (zs ++ zs')) 
                  (ds ++ ds') 
                  (sortNub (is ++ is')) 
                  (as ++ as')
                  (ps ++ ps')
                  (M.union es es')
  mempty   = Spec [] [] [] [] [] [] [] [] M.empty

instance Functor Def where
  fmap f def = def { ctor = f (ctor def) }

instance Functor (Measure t) where
  fmap f (M n s eqs) = M n s (fmap (fmap f) eqs)

instance Functor (MSpec t) where
  fmap f (MSpec cm mm) = MSpec (fc cm) (fm mm)
     where fc = fmap $ fmap $ fmap f
           fm = fmap $ fmap f 

instance Bifunctor Measure where
  first f (M n s eqs)  = M n (f s) eqs
  second f (M n s eqs) = M n s (fmap f <$> eqs)

instance Bifunctor MSpec   where
  first f (MSpec cm mm) = MSpec cm (fmap (first f) mm)
  second                = fmap 

instance Bifunctor Spec    where
  first f (Spec ms ss is x0 x1 x2 x3 x4 x5) 
    = Spec { measures   = first  f <$> ms
           , sigs       = second f <$> ss
           , invariants =        f <$> is
           , imports    = x0 
           , dataDecls  = x1
           , includes   = x2
           , aliases    = x3
           , paliases   = x4
           , embeds     = x5
           }
  second f (Spec ms x0 x1 x2 x3 x4 x5 x5' x6) 
    = Spec { measures   = fmap (second f) ms
           , sigs       = x0 
           , invariants = x1
           , imports    = x2
           , dataDecls  = x3
           , includes   = x4
           , aliases    = x5
           , paliases   = x5'
           , embeds     = x6
           }

instance Fixpoint Body where
  toFix (E e)   = toFix e  
  toFix (P p)   = toFix p
  toFix (R v p) = braces (toFix v <+> text "|" <+> toFix p)   

instance Fixpoint a => Fixpoint (Def a) where
  toFix (Def m c bs body) = toFix m <> text " " <> cbsd <> text " = " <> toFix body   
    where cbsd = parens (toFix c <> hsep (toFix `fmap` bs))

instance (Fixpoint t, Fixpoint a) => Fixpoint (Measure t a) where
  toFix (M n s eqs) =  toFix n <> text "::" <> toFix s
                    $$ vcat (toFix `fmap` eqs)

instance (Fixpoint t, Fixpoint a) => Fixpoint (MSpec t a) where
  toFix =  vcat . fmap toFix . fmap snd . M.toList . measMap

instance (Fixpoint t , Fixpoint a) => Show (Measure t a) where
  show = showFix

mapTy :: (tya -> tyb) -> Measure tya c -> Measure tyb c
mapTy f (M n ty eqs) = M n (f ty) eqs

dataConTypes :: MSpec RefType DataCon -> ([(Var, RefType)], [(Symbol, RefType)])
dataConTypes  s = (expandSnd ctorTys, measTys)
  where measTys = [(name m, sort m) | m <- M.elems $ measMap s]
        ctorTys = [(defsVar ds, defsTy ds) | (_, ds) <- M.toList $ ctorMap s]
        defsTy  = foldl1' meet . fmap defRefType 
        defsVar = dataConImplicitIds . ctor . safeHead "defsVar" 

defRefType :: Def DataCon -> RefType
defRefType (Def f dc xs body) = mkArrow as [] xts t'
  where as  = RTV <$> dataConUnivTyVars dc
        xts = safeZip "defRefType" xs $ ofType `fmap` dataConOrigArgTys dc
        t'  = refineWithCtorBody dc f body t 
        t   = ofType $ dataConOrigResTy dc

refineWithCtorBody dc f body t = 
  case stripRTypeBase t of 
    Just (FReft (Reft (v, _))) ->
      strengthen t $ reft (v, [RConc $ bodyPred (EApp f [EVar v]) body])
    Nothing -> 
      errorstar $ "measure mismatch " ++ showFix f ++ " on con " ++ O.showPpr dc


bodyPred ::  Expr -> Body -> Pred
bodyPred fv (E e)    = PAtom Eq fv e
bodyPred fv (P p)    = PIff  (PBexp fv) p 
bodyPred fv (R v' p) = subst1 p (v', fv)


-------------------------------------------------------------------------------
----------- Refinement Type Aliases -------------------------------------------
-------------------------------------------------------------------------------

data RTEnv   = RTE { typeAliases :: M.HashMap String (RTAlias String BareType)
                   , predAliases :: M.HashMap String (RTAlias Symbol Pred)
                   }

expandRTAliases :: Spec BareType Symbol -> Spec BareType Symbol
expandRTAliases sp = sp { sigs       = [ (x, generalize $ expandRTAlias env t) | (x, t) <- sigs sp       ] }
                        { dataDecls  = [ expandRTAliasDataDecl env dc          | dc     <- dataDecls sp  ] } 
                        { invariants = [ generalize $ expandRTAlias env t      | t      <- invariants sp ] }
                        { measures   = [ expandRTAliasMeasure env m            | m      <- measures sp   ] } 
  where env        = makeRTEnv (aliases sp) (paliases sp)
        
        
expandRTAliasMeasure env m     = m { sort = generalize (sort m) } 
                                   { eqns = expandRTAliasDef env <$> (eqns m) }

expandRTAliasDef  :: RTEnv -> Def Symbol -> Def Symbol
expandRTAliasDef   env d       = d { body = expandRTAliasBody env (body d) }


expandRTAliasBody  :: RTEnv -> Body -> Body
expandRTAliasBody  env (P p)   = P   (expPAlias env p) 
expandRTAliasBody  env (R x p) = R x (expPAlias env p)
expandRTAliasBody  env b       = b
   
expPAlias :: RTEnv -> Pred -> Pred
expPAlias env = expandPAlias (\_ _ -> id) [] (predAliases env)


-- | Constructing the Alias Environment

makeRTEnv     :: [RTAlias String BareType] -> [RTAlias Symbol Pred] -> RTEnv
makeRTEnv  rts pts = RTE typeMap predMap
  where typeMap    = makeAliasMap expandRTAliasE rts
        predMap    = makeAliasMap expandRPAliasE pts

makeAliasMap exp xts = expBody <$> env0
  where env0      = safeFromList "makeAliasMap" [(rtName x, x) | x <- xts]
        expBody z = z { rtBody = exp env0 $ rtBody z }   

-- | Using the Alias Environment to Expand Definitions

expandRTAlias       :: RTEnv -> BareType -> BareType
expandRTAlias env   = expReft . expType 
  where expReft = fmap (txPredReft expPred) 
        expType = expandAlias  (\_ _ -> id) [] (typeAliases env)
        expPred = expandPAlias (\_ _ -> id) [] (predAliases env)

txPredReft f = fmap  (txPredReft' f)
  where txPredReft f (Reft (v, ras)) = Reft (v, txPredRefa f <$> ras)
        txPredRefa f (RConc p)       = RConc (f p)
        txPredRefa _ z               = z
        txPredReft' f (FReft r)      = FReft $ txPredReft f r
        txPredReft' f (FSReft s r)   = FSReft s $ txPredReft f r
       

expandRTAliasDataDecl env dc = dc {tycDCons = dcons' }  
  where dcons' = map (mapSnd (map (mapSnd (expandRTAlias env)))) (tycDCons dc) 


-- | Using the Alias Environment to Expand Definitions

expandRPAliasE  :: M.HashMap String (RTAlias Symbol Pred) -> Pred -> Pred
expandRPAliasE  = go []
  where go = expandPAlias go

expandRTAliasE  :: M.HashMap String (RTAlias String BareType) -> BareType -> BareType 
expandRTAliasE = go []
  where go = expandAlias go

-- expandRTAlias' env t = traceShow ("expandRTAlias t = " ++ showPpr t) $ expandRTAlias env t

expandAlias f s env = go s 
  where go s (RApp c ts rs r)
          | c `elem` s        = errorstar $ "Cyclic Reftype Alias Definition: " ++ show (c:s)
          | c `M.member` env  = assert (null rs) $ expandRTApp (f (c:s) env) env c ts r
          | otherwise         = RApp c (go s <$> ts) rs r 
        go s (RAllT a t)      = RAllT a (go s t)
        go s (RAllP a t)      = RAllP a (go s t)
        go s (RFun x t t' r)  = RFun x (go s t) (go s t') r
        go s (RAppTy t t' r)  = RAppTy (go s t) (go s t') r
        go s (RCls c ts)      = RCls c (go s <$> ts) 
        go _ t                = t


expandRTApp tx env c args r
  | length args == (length αs) + (length εs)
  = subst su  $ (`strengthen` r) $ subsTyVars_meet αts $ tx $ rtBody rta
  | otherwise
  = errorstar $ "Malformed Type-Alias Application" ++ msg
  where 
    αts       = zipWith (\α t -> (α, toRSort t, t)) αs ts
    su        = mkSubst $ zip (stringSymbol <$> εs) es
    αs        = rtTArgs rta 
    εs        = rtVArgs rta 
    rta       = env M.! c
    msg       = showFix (RApp c args [] r) ++ "in " ++ show rta 
    (ts, es_) = splitAt (length αs) args
    es        = map exprArg es_
    -- | exprArg converts a tyVar to an exprVar because parser cannot tell 
    exprArg (RExprArg e) = e
    exprArg (RVar x _)   = EVar (stringSymbol x)
    exprArg _            = errorstar $ "Unexpected expression parameter: " ++ msg 


-- expandRTApp tx env c args r
--   | (length ts == length αs && length es == length εs) 
--   = subst su $ (`strengthen` r) $ subsTyVars_meet αts $ tx $ rtBody rta
--     -- ((subsTyVars_meet αts (tx (rtBody rta))) `strengthen` r) 
--   | otherwise
--   = errorstar $ "Malformed Type-Alias Application" ++ msg
--   where 
--     (es, ts) = splitRTArgs args
--     αts      = zipWith (\α t -> (α, toRSort t, t)) αs ts
--     su       = mkSubst $ zip (stringSymbol <$> εs) es
--     αs       = rtTArgs rta 
--     εs       = rtVArgs rta 
--     rta      = env M.! c
--     msg      = showPpr (RApp c args [] r)  
-- 
-- splitRTArgs         = partitionEithers . map sp 
--   where 
--     sp (RExprArg e) = Left e
--     sp t            = Right t



expandPAlias tx s env = go s 
  where 
    go s p@(PBexp (EApp f es))  
      | f `elem` s                = errorstar $ "Cyclic Predicate Alias Definition: " ++ show (f:s)
      | (symbolString f) `M.member` env  
                                  = expandRPApp (tx (f:s) env) env f es
      | otherwise                 = p
    go s (PAnd ps)                = PAnd (go s <$> ps)
    go s (POr  ps)                = POr  (go s <$> ps)
    go s (PNot p)                 = PNot (go s p)
    go s (PImp p q)               = PImp (go s p) (go s q)
    go s (PIff p q)               = PIff (go s p) (go s q)
    go s (PAll xts p)             = PAll xts (go s p)
    go _ p                        = p

expandRPApp tx env f es = tx (subst su $ rtBody def) 
  where su   = mkSubst $ safeZip msg (rtVArgs def) es 
        def  = env M.! (symbolString f)
        msg  = "expandRPApp: " ++ show (EApp f es) 
