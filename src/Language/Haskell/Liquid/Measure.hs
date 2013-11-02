{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE UndecidableInstances   #-}

module Language.Haskell.Liquid.Measure (  
    Spec (..)
  , BareSpec  
  , MSpec (..)
  , mkM, mkMSpec
  , qualifySpec
  , mapTy
  , dataConTypes
  , defRefType
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
import Data.List (foldl1', union)
import Data.Either (partitionEithers)
import Data.Bifunctor
import Control.Applicative      ((<$>))
import Control.Exception        (assert)

import Language.Fixpoint.Misc
import Language.Fixpoint.Types hiding (Def)
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
  , lvars      :: ![(LocSymbol)]                -- ^ Variables that should be checked in the environment they are used
  , lazy       :: !(S.HashSet Symbol)           -- ^ Ignore Termination Check in these Functions
  , pragmas    :: ![Located String]             -- ^ Command-line configurations passed in through source
  , cmeasures  :: ![Measure ty ()]              -- ^ Measures attached to a type-class
  , imeasures  :: ![Measure ty bndr]            -- ^ Mappings from (measure,type) -> measure
  , classes    :: ![RClass ty]                  -- ^ Refined Type-Classes
  }


-- MOVE TO TYPES
data MSpec ty ctor = MSpec { 
    ctorMap  :: M.HashMap Symbol [Def ctor]
  , measMap  :: M.HashMap Symbol (Measure ty ctor)
  , cmeasMap :: M.HashMap Symbol (Measure ty ())
  , imeas    :: ![Measure ty ctor]
  }

instance Monoid (MSpec ty ctor) where
  mempty = MSpec M.empty M.empty M.empty []

  (MSpec c1 m1 cm1 im1) `mappend` (MSpec c2 m2 cm2 im2) =
    MSpec (M.unionWith (++) c1 c2) (m1 `M.union` m2)
          (cm1 `M.union` cm2) (im1 ++ im2)


qualifySpec name sp = sp { sigs = [ (qualifySymbol name <$> x, t) | (x, t) <- sigs sp] }

mkM ::  LocSymbol -> ty -> [Def bndr] -> Measure ty bndr
mkM name typ eqns 
  | all ((name ==) . measure) eqns
  = M name typ eqns
  | otherwise
  = errorstar $ "invalid measure definition for " ++ (show name)

-- mkMSpec :: [Measure ty Symbol] -> [Measure ty ()] -> [IMeasure Type]
--         -> MSpec ty Symbol
mkMSpec ms cms ims = MSpec cm mm cmm ims
  where 
    cm     = groupMap ctor $ concatMap eqns (ms'++ims)
    mm     = M.fromList [(val $ name m, m) | m <- ms' ]
    cmm    = M.fromList [(val $ name m, m) | m <- cms ]
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
  mappend (Spec xs ys invs zs ds is as ps es qs drs lvs ss gs cms ims cls)
          (Spec xs' ys' invs' zs' ds' is' as' ps' es' qs' drs' lvs' ss' gs' cms' ims' cls')
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
                  (lvs ++ lvs')
                  (S.union ss ss')
                  (gs ++ gs')
                  (cms ++ cms')
                  (ims ++ ims')
                  (cls ++ cls')
  mempty   = Spec [] [] [] [] [] [] [] [] M.empty [] [] [] S.empty [] [] [] []

-- MOVE TO TYPES
instance Functor Def where
  fmap f def = def { ctor = f (ctor def) }

-- MOVE TO TYPES
instance Functor (Measure t) where
  fmap f (M n s eqs) = M n s (fmap (fmap f) eqs)

instance Functor CMeasure where
  fmap f (CM n t) = CM n (f t)

-- MOVE TO TYPES
instance Functor (MSpec t) where
  fmap f (MSpec c m cm im) = MSpec (fc c) (fm m) cm (fmap (fmap f) im)
     where fc = fmap $ fmap $ fmap f
           fm = fmap $ fmap f 

-- MOVE TO TYPES
instance Bifunctor Measure where
  first f (M n s eqs)  = M n (f s) eqs
  second f (M n s eqs) = M n s (fmap f <$> eqs)

-- MOVE TO TYPES
instance Bifunctor MSpec   where
  first f (MSpec c m cm im) = MSpec c (fmap (first f) m) (fmap (first f) cm) (fmap (first f) im)
  second                    = fmap

-- MOVE TO TYPES
instance Bifunctor Spec    where
  first f (Spec ms ss is x0 x1 x2 x3 x4 x5 x6 x7 x7a x8 x9 cms ims cls)
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
           , lvars      = x7a
           , lazy       = x8
           , pragmas    = x9
           , cmeasures  = first f <$> cms
           , imeasures  = first f <$> ims
           , classes    = fmap f <$> cls
           }
  second f (Spec ms x0 x1 x2 x3 x4 x5 x5' x6 x7 x8 x8a x9 x10 x11 ims x12)
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
           , lvars      = x8a
           , lazy       = x9
           , pragmas    = x10
           , cmeasures  = x11
           , imeasures  = fmap (second f) ims
           , classes    = x12
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
  pprint (M n s eqs) =  pprint n <> text " :: " <> pprint s
                     $$ vcat (pprint `fmap` eqs)

-- MOVE TO TYPES
instance (PPrint t, PPrint a) => PPrint (MSpec t a) where
  pprint =  vcat . fmap pprint . fmap snd . M.toList . measMap

-- MOVE TO TYPES
instance PPrint (Measure t a) => Show (Measure t a) where
  show = showpp

instance PPrint t => PPrint (CMeasure t) where
  pprint (CM n s) =  pprint n <> text " :: " <> pprint s
                 -- $$ vcat ((\(i,m) -> pprint (IM n i m)) <$> is)

instance PPrint (CMeasure t) => Show (CMeasure t) where
  show = showpp

-- MOVE TO TYPES
mapTy :: (tya -> tyb) -> Measure tya c -> Measure tyb c
mapTy f (M n ty eqs) = M n (f ty) eqs

dataConTypes :: MSpec RefType DataCon -> ([(Var, RefType)], [(LocSymbol, RefType)])
dataConTypes  s = (ctorTys, measTys)
  where 
    measTys     = [(name m, sort m) | m <- M.elems (measMap s) ++ imeas s]
    ctorTys     = concatMap mkDataConIdsTy [(defsVar ds, defsTy ds)
                                           | (_, ds) <- M.toList (ctorMap s)
                                                       ]
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


