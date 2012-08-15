{-# LANGUAGE DeriveDataTypeable, RankNTypes, GADTs #-}

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
  , RTAlias (..)
  , expandRTAliases
  ) where

import GHC
import Var
import Outputable
import DataCon
import Data.Map hiding (null, partition)
import Data.Data
import Data.Monoid hiding ((<>))
import Data.List (foldl1', partition)
import Data.Bifunctor
import Control.Applicative      ((<$>))

import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType

data Spec ty bndr  = Spec { 
    measures   :: ![Measure ty bndr]     -- User-defined properties for ADTs
  , sigs       :: ![(Symbol, ty)]        -- Imported functions and types   
  , invariants :: ![ty]                  -- Data type invariants  
  , imports    :: ![Symbol]              -- Loaded spec module names
  , dataDecls  :: ![DataDecl]            -- Predicated data definitions 
  , includes   :: ![FilePath]            -- Included qualifier files
  , aliases    :: ![RTAlias]             -- RefType aliases
  } deriving (Data, Typeable)

data MSpec ty bndr = MSpec { 
    ctorMap :: Map Symbol [Def bndr]
  , measMap :: Map Symbol (Measure ty bndr) 
  } deriving (Data, Typeable)

data Measure ty bndr = M { 
    name :: Symbol
  , sort :: ty
  , eqns :: [Def bndr]
  } deriving (Data, Typeable)

data Def bndr 
  = Def { 
    measure :: Symbol
  , ctor    :: bndr
  , binds   :: [Symbol]
  , body    :: Body
  } deriving (Data, Typeable)

data Body 
  = E Expr 
  | P Pred
  deriving (Data, Typeable)

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
        mm  = fromList [(name m, m) | m <- ms' ]
        ms' = checkFail "Duplicate Measure Definition" (distinct . fmap name) ms

instance Monoid (Spec ty bndr) where
  mappend (Spec xs ys invs zs ds is as) (Spec xs' ys' invs' zs' ds' is' as')
           = Spec (xs ++ xs') 
                  (ys ++ ys') 
                  (invs ++ invs') 
                  (nubSort (zs ++ zs')) 
                  (ds ++ ds') 
                  (nubSort (is ++ is')) 
                  (as ++ as')
  mempty   = Spec [] [] [] [] [] [] []

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
  first f (Spec ms ss is x0 x1 x2 x3) 
    = Spec { measures   = first  f <$> ms
           , sigs       = second f <$> ss
           , invariants =        f <$> is
           , imports    = x0 
           , dataDecls  = x1
           , includes   = x2
           , aliases    = x3
           }
  second f (Spec ms x0 x1 x2 x3 x4 x5) 
    = Spec { measures   = fmap (second f) ms
           , sigs       = x0 
           , invariants = x1
           , imports    = x2
           , dataDecls  = x3
           , includes   = x4
           , aliases    = x5
           }

instance Outputable Body where
  ppr (E e) = toFix e  
  ppr (P p) = toFix p

instance Outputable a => Outputable (Def a) where
  ppr (Def m c bs body) = ppr m <> text " " <> pprPat (c, bs) <> text " = " <> ppr body   
    where pprPat (c, bs) = parens (ppr c <> hsep (ppr `fmap` bs))

instance (Outputable t, Outputable a) => Outputable (Measure t a) where
  ppr (M n s eqs) =  ppr n <> text "::" <> ppr s
                  $$ vcat (ppr `fmap` eqs)

instance (Outputable t, Outputable a) => Outputable (MSpec t a) where
  ppr =  vcat . fmap ppr . fmap snd . toList . measMap

instance (Outputable t, Outputable a) => Show (Measure t a) where
  show = showPpr

mapTy :: (tya -> tyb) -> Measure tya c -> Measure tyb c
mapTy f (M n ty eqs) = M n (f ty) eqs




dataConTypes :: MSpec RefType DataCon -> ([(Var, RefType)], [(Symbol, RefType)])
dataConTypes s = (ctorTys, measTys)
  where measTys = [(name m, sort m) | m <- elems $ measMap s]
        ctorTys = [(defsVar ds, defsTy ds) | (_, ds) <- toList $ ctorMap s]
        defsTy  = foldl1' meet {-strengthenRefType-} . fmap defRefType 
        defsVar = dataConWorkId . ctor . safeHead "defsVar" 

defRefType :: Def DataCon -> RefType
defRefType (Def f dc xs body) = mkArrow as xts t'
  where as  = RTV <$> dataConUnivTyVars dc
        xts = safeZip "defRefType" xs $ ofType `fmap` dataConOrigArgTys dc
        t'  = refineWithCtorBody dc f body t 
        t   = ofType $ dataConOrigResTy dc

refineWithCtorBody dc f body t = 
  case stripRTypeBase t of 
    Just (Reft (v, ras)) ->
      strengthen t $ Reft (v, [RConc $ bodyPred v body])
    Nothing -> 
      errorstar $ "measure mismatch " ++ showPpr f ++ " on con " ++ showPpr dc
  where bodyPred v (E e) = PAtom Eq (EApp f [EVar v]) e
        bodyPred v (P p) = PIff  (PBexp (EApp f [EVar v])) p 

--measuresSpec ::  [Measure ty bndr] -> Spec ty bndr
--measuresSpec ms = Spec ms' bs 
--  where (ms', ms'') = partition (not . null . eqns) ms
--        bs          = [(name m, sort m) | m <- ms'']

-----------------------------------------------------------------------------
------ Reftype Aliases ------------------------------------------------------
-----------------------------------------------------------------------------

data RTAlias   = RTA { rtName :: String
                     , rtArgs :: [String]
                     , rtBody :: BareType
                     } deriving (Data, Typeable)

type RTEnv     = Map String RTAlias

makeRTEnv      :: [RTAlias] -> RTEnv      
makeRTEnv      = error "TODO: makeRTEnv"

expandRTAlias  :: RTEnv -> BareType -> BareType 
expandRTAlias  = error "TODO: expandRTAlias"

expandRTAliases  :: Spec BareType Symbol -> Spec BareType Symbol
expandRTAliases sp = first (expandRTAlias env) sp
                     where env = makeRTEnv (aliases sp)

