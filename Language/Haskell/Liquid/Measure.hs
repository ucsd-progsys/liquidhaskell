{- LANGUAGE DeriveDataTypeable, RankNTypes, GADTs -}

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
import Outputable hiding (empty)
import DataCon
import qualified Data.HashMap.Strict as M 
-- import Data.Data
import Data.Monoid hiding ((<>))
import Data.List (foldl1')
import Data.Bifunctor
import Control.Applicative      ((<$>))
import Control.Exception        (assert)

import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint
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
  } -- deriving (Data, Typeable)

data Body 
  = E Expr          -- ^ Measure Refinement: {v | v = e } 
  | P Pred          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Pred   -- ^ Measure Refinement: {v | p}
  -- deriving (Data, Typeable)

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

instance Outputable Body where
  ppr (E e)   = toFix e  
  ppr (P p)   = toFix p
  ppr (R v p) = braces (ppr v <+> text "|" <+> toFix p)   

instance Outputable a => Outputable (Def a) where
  ppr (Def m c bs body) = ppr m <> text " " <> pprPat (c, bs) <> text " = " <> ppr body   
    where pprPat (c, bs) = parens (ppr c <> hsep (ppr `fmap` bs))

instance (Outputable t, Outputable a) => Outputable (Measure t a) where
  ppr (M n s eqs) =  ppr n <> text "::" <> ppr s
                  $$ vcat (ppr `fmap` eqs)

instance (Outputable t, Outputable a) => Outputable (MSpec t a) where
  ppr =  vcat . fmap ppr . fmap snd . M.toList . measMap

instance (Outputable t, Outputable a) => Show (Measure t a) where
  show = showPpr

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
    Just (Reft (v, _)) ->
      strengthen t $ Reft (v, [RConc $ bodyPred (EApp f [EVar v]) body])
    Nothing -> 
      errorstar $ "measure mismatch " ++ showPpr f ++ " on con " ++ showPpr dc


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
expandRTAliases sp = sp { sigs = sigs' } { dataDecls = ds' }
  where env   = makeRTEnv (aliases sp) (paliases sp)
        sigs' = [(x, expandRTAlias env t)     | (x, t) <- sigs sp     ]
        ds'   = [expandRTAliasDataDecl env dc | dc     <- dataDecls sp] 

-- | Constructing the Alias Environment

makeRTEnv     :: [RTAlias String BareType] -> [RTAlias Symbol Pred] -> RTEnv
makeRTEnv  rts pts = RTE typeMap predMap
  where typeMap    = makeAliasMap expandRTAliasE rts
        predMap    = makeAliasMap expandRPAliasE pts

makeAliasMap exp xts = expBody <$> env0
  where env0      = safeFromList "makeAliasMap" [(rtName x, x) | x <- xts]
        expBody z = z { rtBody = exp env0 $ rtBody z }   

-- makeRTEnv rts pts = rTEnv nrts' npts' 
--   where nrts      = [(rtName x, x) | x <- rts]
--         npts      = [(rtName x, x) | x <- pts]
--         env0      = rTEnv nrts npts 
--         nrts'     = map (second (expBody expandRTAliasE (typeAliases env0))) nrts 
--         npts'     = map (second (expBody expandRTAliasE (predAliases env0))) npts
-- 
-- rTEnv nrts npts   = RTEnv { typeAliases = safeFromList "Reftype Aliases" nrts  
--                           , predAliases = safeFromList "Predicate Aliases" npts } 


-- | Using the Alias Environment to Expand Definitions

expandRTAlias       :: RTEnv -> BareType -> BareType
expandRTAlias env   = expReft . expType 
  where expReft = mapReft (txPredReft expPred) 
        expType = expandAlias  (\_ _ -> id) [] (typeAliases env)
        expPred = expandPAlias (\_ _ -> id) [] (predAliases env)

txPredReft f = fmap (txPredReft f)
  where txPredReft f (Reft (v, ras)) = Reft (v, txPredRefa f <$> ras)
        txPredRefa f (RConc p)       = RConc (f p)
        txPredRefa _ z               = z

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
        go s (RCls c ts)      = RCls c (go s <$> ts) 
        go _ t                = t

expandRTApp tx env c ts r
  = (subsTyVars_meet αts' t') `strengthen` r
    where t'   = tx (rtBody rta)
          αts' = assert (length αs == length αts) αts
          αts  = zipWith (\α t -> (α, toRSort t, t)) αs ts
          αs   = rtArgs rta
          rta  = env M.! c

expandPAlias tx s env = go s 
  where 
    go s p@(PBexp (EApp f es))  
      | f `elem` s                = errorstar $ "Cyclic Predicate Alias Definition: " ++ show (f:s)
      | (symbolString f) `M.member` env  
                                  = expandRPApp (tx (f:s) env) env f es
      | otherwise                 = p
    go s PTrue                = PTrue
    go s PFalse               = PFalse
    go s (PAnd ps)            = PAnd (go s <$> ps)
    go s (POr  ps)            = POr  (go s <$> ps)
    go s (PNot p)             = PNot (go s p)
    go s (PImp p q)           = PImp (go s p) (go s q)
    go s (PIff p q)           = PIff (go s p) (go s q)
    go s (PAll xts p)         = PAll xts (go s p)
    go _ p@(PAtom _ _ _)      = p
    go _ p@(PTop)             = p


expandRPApp tx env f es = tx (subst su $ rtBody def) 
  where su   = mkSubst $ safeZip msg (rtArgs def) es 
        def  = env M.! (symbolString f)
        msg  = "expandRPApp: " ++ show (EApp f es) 
