{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE UndecidableInstances   #-}

module Language.Haskell.Liquid.Measure (  
    Spec (..)
  , BareSpec  
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

import GHC hiding (Located)
import Var
import qualified Outputable as O 
import Text.PrettyPrint.HughesPJ hiding (first)
import Text.Printf (printf)
import DataCon
import qualified Data.HashMap.Strict as M 
import qualified Data.HashSet        as S 
import Data.Monoid hiding ((<>))
import Data.List (foldl1')
import Data.Either (partitionEithers)
import Data.Bifunctor
import Control.Applicative      ((<$>))
import Control.Exception        (assert)

import Language.Fixpoint.Misc
import Language.Fixpoint.Types
import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Types    hiding (GhcInfo(..), GhcSpec (..))
import Language.Haskell.Liquid.RefType

-- MOVE TO TYPES
type BareSpec      = Spec BareType Symbol

data Spec ty bndr  = Spec { 
    measures   :: ![Measure ty bndr]            -- ^ User-defined properties for ADTs
  , sigs       :: ![(LocSymbol, ty)]            -- ^ Imported functions and types   
  , invariants :: ![Located ty]                 -- ^ Data type invariants  
  , imports    :: ![Symbol]                     -- ^ Loaded spec module names
  , dataDecls  :: ![DataDecl]                   -- ^ Predicated data definitions 
  , includes   :: ![FilePath]                   -- ^ Included qualifier files
  , aliases    :: ![RTAlias String BareType]    -- ^ RefType aliases
  , paliases   :: ![RTAlias Symbol Pred]        -- ^ Refinement/Predicate aliases
  , embeds     :: !(TCEmb (Located String))     -- ^ GHC-Tycon-to-fixpoint Tycon map
  , qualifiers :: ![Qualifier]                  -- ^ Qualifiers in source/spec files
  , decr       :: ![(LocSymbol, [Int])]         -- ^ Information on decreasing arguments
  , lazy       :: !(S.HashSet Symbol)           -- ^ Ignore Termination Check in these Functions
  , pragmas    :: ![Located String]             -- ^ Command-line configurations passed in through source
  } 


-- MOVE TO TYPES
data MSpec ty ctor = MSpec { 
    ctorMap :: M.HashMap Symbol [Def ctor]
  , measMap :: M.HashMap Symbol (Measure ty ctor) 
  }

-- MOVE TO TYPES
data Measure ty ctor = M { 
    name :: LocSymbol
  , sort :: ty
  , eqns :: [Def ctor]
  } 

-- MOVE TO TYPES
data Def ctor 
  = Def { 
    measure :: LocSymbol
  , ctor    :: ctor 
  , binds   :: [Symbol]
  , body    :: Body
  } deriving (Show)

-- MOVE TO TYPES
data Body 
  = E Expr          -- ^ Measure Refinement: {v | v = e } 
  | P Pred          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Pred   -- ^ Measure Refinement: {v | p}
  deriving (Show)

qualifySpec name sp = sp { sigs = [ (qualifySymbol name <$> x, t) | (x, t) <- sigs sp] }

mkM ::  LocSymbol -> ty -> [Def bndr] -> Measure ty bndr
mkM name typ eqns 
  | all ((name ==) . measure) eqns
  = M name typ eqns
  | otherwise
  = errorstar $ "invalid measure definition for " ++ (show name)

-- mkMSpec ::  [Measure ty Symbol] -> MSpec ty Symbol
mkMSpec ms = MSpec cm mm 
  where 
    cm     = groupMap ctor $ concatMap eqns ms'
    mm     = M.fromList [(val $ name m, m) | m <- ms' ]
    ms'    = checkDuplicateMeasure ms
    -- ms'    = checkFail "Duplicate Measure Definition" (distinct . fmap name) ms

checkDuplicateMeasure ms 
  = case M.toList dups of 
      []         -> ms
      mms        -> errorstar $ concatMap err mms 
    where 
      gms        = group [(name m , m) | m <- ms]
      dups       = M.filter ((1 <) . length) gms
      err (m,ms) = printf "\nDuplicate Measure Definitions for %s\n%s" (showpp m) (showpp $ map (loc . name) ms)




-- MOVE TO TYPES
instance Monoid (Spec ty bndr) where
  mappend (Spec xs ys invs zs ds is as ps es qs drs ss gs) 
          (Spec xs' ys' invs' zs' ds' is' as' ps' es' qs' drs' ss' gs')
           = Spec (xs ++ xs') 
                  (ys ++ ys') 
                  (invs ++ invs') 
                  (sortNub (zs ++ zs')) 
                  (ds ++ ds') 
                  (sortNub (is ++ is')) 
                  (as ++ as')
                  (ps ++ ps')
                  (M.union es es')
                  (qs ++ qs')
                  (drs ++ drs')
                  (S.union ss ss')
                  (gs ++ gs')
  mempty   = Spec [] [] [] [] [] [] [] [] M.empty [] [] S.empty []

-- MOVE TO TYPES
instance Functor Def where
  fmap f def = def { ctor = f (ctor def) }

-- MOVE TO TYPES
instance Functor (Measure t) where
  fmap f (M n s eqs) = M n s (fmap (fmap f) eqs)

-- MOVE TO TYPES
instance Functor (MSpec t) where
  fmap f (MSpec cm mm) = MSpec (fc cm) (fm mm)
     where fc = fmap $ fmap $ fmap f
           fm = fmap $ fmap f 

-- MOVE TO TYPES
instance Bifunctor Measure where
  first f (M n s eqs)  = M n (f s) eqs
  second f (M n s eqs) = M n s (fmap f <$> eqs)

-- MOVE TO TYPES
instance Bifunctor MSpec   where
  first f (MSpec cm mm) = MSpec cm (fmap (first f) mm)
  second                = fmap 

-- MOVE TO TYPES
instance Bifunctor Spec    where
  first f (Spec ms ss is x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) 
    = Spec { measures   = first  f <$> ms
           , sigs       = second f <$> ss
           , invariants = fmap   f <$> is
           , imports    = x0 
           , dataDecls  = x1
           , includes   = x2
           , aliases    = x3
           , paliases   = x4
           , embeds     = x5
           , qualifiers = x6
           , decr       = x7
           , lazy       = x8
           , pragmas    = x9 
           }
  second f (Spec ms x0 x1 x2 x3 x4 x5 x5' x6 x7 x8 x9 x10) 
    = Spec { measures   = fmap (second f) ms
           , sigs       = x0 
           , invariants = x1
           , imports    = x2
           , dataDecls  = x3
           , includes   = x4
           , aliases    = x5
           , paliases   = x5'
           , embeds     = x6
           , qualifiers = x7
           , decr       = x8
           , lazy       = x9
           , pragmas    = x10
           }

-- MOVE TO TYPES
instance PPrint Body where
  pprint (E e)   = pprint e  
  pprint (P p)   = pprint p
  pprint (R v p) = braces (pprint v <+> text "|" <+> pprint p)   

-- instance PPrint a => Fixpoint (PPrint a) where
--   toFix (BDc c)  = toFix c
--   toFix (BTup n) = parens $ toFix n

-- MOVE TO TYPES
instance PPrint a => PPrint (Def a) where
  pprint (Def m c bs body) = pprint m <> text " " <> cbsd <> text " = " <> pprint body   
    where cbsd = parens (pprint c <> hsep (pprint `fmap` bs))

-- MOVE TO TYPES
instance (PPrint t, PPrint a) => PPrint (Measure t a) where
  pprint (M n s eqs) =  pprint n <> text "::" <> pprint s
                     $$ vcat (pprint `fmap` eqs)

-- MOVE TO TYPES
instance (PPrint t, PPrint a) => PPrint (MSpec t a) where
  pprint =  vcat . fmap pprint . fmap snd . M.toList . measMap

-- MOVE TO TYPES
instance PPrint (Measure t a) => Show (Measure t a) where
  show = showpp

-- MOVE TO TYPES
mapTy :: (tya -> tyb) -> Measure tya c -> Measure tyb c
mapTy f (M n ty eqs) = M n (f ty) eqs

dataConTypes :: MSpec RefType DataCon -> ([(Var, RefType)], [(LocSymbol, RefType)])
dataConTypes  s = (ctorTys, measTys)
  where 
    measTys     = [(name m, sort m) | m <- M.elems $ measMap s]
    ctorTys     = concatMap mkDataConIdsTy [(defsVar ds, defsTy ds) | (_, ds) <- M.toList $ ctorMap s]
    defsTy      = foldl1' meet . fmap defRefType 
    defsVar     = ctor . safeHead "defsVar" 

defRefType :: Def DataCon -> RefType
defRefType (Def f dc xs body) = mkArrow as [] xts t'
  where 
    as  = RTV <$> dataConUnivTyVars dc
    xts = safeZip msg xs $ ofType `fmap` dataConOrigArgTys dc
    t'  = refineWithCtorBody dc f body t 
    t   = ofType $ dataConOrigResTy dc
    msg = "defRefType dc = " ++ showPpr dc 


refineWithCtorBody dc (Loc _ f) body t = 
  case stripRTypeBase t of 
    Just (Reft (v, _)) ->
      strengthen t $ Reft (v, [RConc $ bodyPred (EApp f [eVar v]) body])
    Nothing -> 
      errorstar $ "measure mismatch " ++ showpp f ++ " on con " ++ showPpr dc


bodyPred ::  Expr -> Body -> Pred
bodyPred fv (E e)    = PAtom Eq fv e
bodyPred fv (P p)    = PIff  (PBexp fv) p 
bodyPred fv (R v' p) = subst1 p (v', fv)


-------------------------------------------------------------------------------
----------- Refinement Type Aliases -------------------------------------------
-------------------------------------------------------------------------------

-- MOVE TO TYPES
data RTEnv   = RTE { typeAliases :: M.HashMap String (RTAlias String BareType)
                   , predAliases :: M.HashMap String (RTAlias Symbol Pred)
                   }

expandRTAliases    :: Spec BareType Symbol -> Spec BareType Symbol
expandRTAliases sp = sp { sigs       = [ (x, generalize $ expandRTAlias env t)  | (x, t) <- sigs sp       ] }
                        { dataDecls  = [ expandRTAliasDataDecl env dc           | dc     <- dataDecls sp  ] } 
                        { invariants = [ generalize <$> expandRTAlias env <$> t | t      <- invariants sp ] }
                        { measures   = [ expandRTAliasMeasure env m             | m      <- measures sp   ] } 
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

expandRTAlias     :: RTEnv -> BareType -> BareType
expandRTAlias env = expReft . expType 
  where 
    expReft       = fmap (txPredReft expPred) 
    expType       = expandAlias  (\_ _ -> id) [] (typeAliases env)
    expPred       = expandPAlias (\_ _ -> id) [] (predAliases env)

txPredReft f      = fmap  (txPredReft f)
  where 
    txPredReft f (Reft (v, ras)) = Reft (v, txPredRefa f <$> ras)
    txPredRefa f (RConc p)       = RConc (f p)
    txPredRefa _ z               = z
       

expandRTAliasDataDecl env dc = dc {tycDCons = dcons' }  
  where 
    dcons' = map (mapSnd (map (mapSnd (expandRTAlias env)))) (tycDCons dc) 


-- | Using the Alias Environment to Expand Definitions

expandRPAliasE  :: M.HashMap String (RTAlias Symbol Pred) -> Pred -> Pred
expandRPAliasE  = go []
  where go = expandPAlias go

expandRTAliasE  :: M.HashMap String (RTAlias String BareType) -> BareType -> BareType 
expandRTAliasE = go []
  where go = expandAlias go


expandAlias f s env = go s 
  where 
    go s (RApp c ts rs r)
      | c `elem` s        = errorstar $ "Cyclic Reftype Alias Definition: " ++ show (c:s)
      | c `M.member` env  = assert (null rs) $ expandRTApp (f (c:s) env) env c (go s <$> ts) r
      | otherwise         = RApp c (go s <$> ts) (go' s <$> rs) r 
    go s (RAllT a t)      = RAllT a (go s t)
    go s (RAllP a t)      = RAllP a (go s t)
    go s (RFun x t t' r)  = RFun x (go s t) (go s t') r
    go s (RAppTy t t' r)  = RAppTy (go s t) (go s t') r
    go s (RCls c ts)      = RCls c (go s <$> ts) 
    go _ t                = t

    go' s z@(RMono _ _)   = z
    go' s (RPoly ss t)    = RPoly ss (go s t)

expandRTApp tx env c args r
  | length args == (length αs) + (length εs)
  = subst su  $ (`strengthen` r) $ subsTyVars_meet αts $ tx $ rtBody rta
  | otherwise
  = errortext $ (text "Malformed Type-Alias Application" $+$ text msg $+$ tshow rta)
  where 
    αts       = zipWith (\α t -> (α, toRSort t, t)) αs ts
    su        = mkSubst $ zip (stringSymbol <$> εs) es
    αs        = rtTArgs rta 
    εs        = rtVArgs rta 
    rta       = env M.! c
    msg       = showpp (RApp c args [] r) 
    (ts, es_) = splitAt (length αs) args
    es        = map (exprArg msg) es_
    
-- | exprArg converts a tyVar to an exprVar because parser cannot tell 
-- HORRIBLE HACK To allow treating upperCase X as value variables X
-- e.g. type Matrix a Row Col = List (List a Row) Col

exprArg _   (RExprArg e)     
  = e
exprArg _   (RVar x _)       
  = EVar (stringSymbol x)
exprArg _   (RApp x [] [] _) 
  = EVar (stringSymbol x)
exprArg msg (RApp f ts [] _) 
  = EApp (stringSymbol f) (exprArg msg <$> ts) 
exprArg msg (RAppTy (RVar f _) t _)   
  = EApp (stringSymbol f) [exprArg msg t]
exprArg msg z 
  = errorstar $ printf "Unexpected expression parameter: %s in %s" (show z) msg 




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
