{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE UndecidableInstances   #-}

module Language.Haskell.Liquid.Measure (  
    Spec (..)
  , BareSpec  
  , MSpec (..)
  , mkM, mkMSpec, mkMSpec'
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
import Data.List (foldl1', union, nub)
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
type BareSpec      = Spec BareType LocSymbol

data Spec ty bndr  = Spec { 
    measures   :: ![Measure ty bndr]            -- ^ User-defined properties for ADTs
  , asmSigs    :: ![(LocSymbol, ty)]            -- ^ Assumed (unchecked) types
  , sigs       :: ![(LocSymbol, ty)]            -- ^ Imported functions and types   
  , localSigs  :: ![(LocSymbol, ty)]            -- ^ Local type signatures
  , invariants :: ![Located ty]                 -- ^ Data type invariants
  , ialiases   :: ![(Located ty, Located ty)]   -- ^ Data type invariants to be checked
  , imports    :: ![Symbol]                     -- ^ Loaded spec module names
  , dataDecls  :: ![DataDecl]                   -- ^ Predicated data definitions 
  , includes   :: ![FilePath]                   -- ^ Included qualifier files
  , aliases    :: ![RTAlias String BareType]    -- ^ RefType aliases
  , paliases   :: ![RTAlias Symbol Pred]        -- ^ Refinement/Predicate aliases
  , embeds     :: !(TCEmb (Located String))     -- ^ GHC-Tycon-to-fixpoint Tycon map
  , qualifiers :: ![Qualifier]                  -- ^ Qualifiers in source/spec files
  , decr       :: ![(LocSymbol, [Int])]         -- ^ Information on decreasing arguments
  , lvars      :: ![(LocSymbol)]                -- ^ Variables that should be checked in the environment they are used
  , lazy       :: !(S.HashSet LocSymbol)        -- ^ Ignore Termination Check in these Functions
  , pragmas    :: ![Located String]             -- ^ Command-line configurations passed in through source
  , cmeasures  :: ![Measure ty ()]              -- ^ Measures attached to a type-class
  , imeasures  :: ![Measure ty bndr]            -- ^ Mappings from (measure,type) -> measure
  , classes    :: ![RClass ty]                  -- ^ Refined Type-Classes
  , termexprs  :: ![(LocSymbol, [Expr])]        -- ^ Terminating Conditions for functions  
  }


-- MOVE TO TYPES
data MSpec ty ctor = MSpec { 
    ctorMap  :: M.HashMap Symbol [Def ctor]
  , measMap  :: M.HashMap LocSymbol (Measure ty ctor)
  , cmeasMap :: M.HashMap LocSymbol (Measure ty ())
  , imeas    :: ![Measure ty ctor]
  }


instance (Show ty, Show ctor, PPrint ctor, PPrint ty) => Show (MSpec ty ctor) where
  show (MSpec ct m cm im) 
    = "\nMSpec:\n" ++ 
      "\nctorMap:\t "  ++ show ct ++ 
      "\nmeasMap:\t "  ++ show m  ++ 
      "\ncmeasMap:\t " ++ show cm ++ 
      "\nimeas:\t "    ++ show im ++ 
      "\n" 

instance Eq ctor => Monoid (MSpec ty ctor) where
  mempty = MSpec M.empty M.empty M.empty []

  (MSpec c1 m1 cm1 im1) `mappend` (MSpec c2 m2 cm2 im2) 
    | null dups 
    = MSpec (M.unionWith (++) c1 c2) (m1 `M.union` m2)
           (cm1 `M.union` cm2) (im1 ++ im2)
    | otherwise 
    = errorstar $ err (head dups)
    where dups = [(k1, k2) | k1 <- M.keys m1 , k2 <- M.keys m2, val k1 == val k2]
          err (k1, k2) = printf "\nDuplicate Measure Definitions for %s\n%s" (showpp k1) (showpp $ map loc [k1, k2])

qualifySpec name sp = sp { sigs      = [ (tx x, t)  | (x, t)  <- sigs sp]
                         , asmSigs   = [ (tx x, t)  | (x, t)  <- asmSigs sp]
--                          , termexprs = [ (tx x, es) | (x, es) <- termexprs sp]
                         }
  where
    tx = fmap (qualifySymbol name)

mkM ::  LocSymbol -> ty -> [Def bndr] -> Measure ty bndr
mkM name typ eqns 
  | all ((name ==) . measure) eqns
  = M name typ eqns
  | otherwise
  = errorstar $ "invalid measure definition for " ++ (show name)

-- mkMSpec :: [Measure ty LocSymbol] -> [Measure ty ()] -> [Measure ty LocSymbol]
--         -> MSpec ty LocSymbol

mkMSpec' ms = MSpec cm mm M.empty []
  where 
    cm     = groupMap (symbol . ctor) $ concatMap eqns ms
    mm     = M.fromList [(name m, m) | m <- ms ]

mkMSpec ms cms ims = MSpec cm mm cmm ims
  where 
    cm     = groupMap (val . ctor) $ concatMap eqns (ms'++ims)
    mm     = M.fromList [(name m, m) | m <- ms' ]
    cmm    = M.fromList [(name m, m) | m <- cms ]
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
  mappend s1 s2
    = Spec { measures   =           measures s1   ++ measures s2
           , asmSigs    =           asmSigs s1    ++ asmSigs s2 
           , sigs       =           sigs s1       ++ sigs s2 
           , localSigs  =           localSigs s1  ++ localSigs s2 
           , invariants =           invariants s1 ++ invariants s2
           , ialiases   =           ialiases s1   ++ ialiases s2
           , imports    = sortNub $ imports s1    ++ imports s2
           , dataDecls  = dataDecls s1            ++ dataDecls s2
           , includes   = sortNub $ includes s1   ++ includes s2
           , aliases    =           aliases s1    ++ aliases s2
           , paliases   =           paliases s1   ++ paliases s2
           , embeds     = M.union   (embeds s1)     (embeds s2)
           , qualifiers =           qualifiers s1 ++ qualifiers s2
           , decr       =           decr s1       ++ decr s2
           , lvars      =           lvars s1      ++ lvars s2
           , lazy       = S.union   (lazy s1)        (lazy s2)
           , pragmas    =           pragmas s1    ++ pragmas s2
           , cmeasures  =           cmeasures s1  ++ cmeasures s2
           , imeasures  =           imeasures s1  ++ imeasures s2
           , classes    =           classes s1    ++ classes s1
           , termexprs  =           termexprs s1  ++ termexprs s2
           }

  mempty
    = Spec { measures   = [] 
           , asmSigs    = [] 
           , sigs       = [] 
           , localSigs  = [] 
           , invariants = []
           , ialiases   = []
           , imports    = []
           , dataDecls  = [] 
           , includes   = [] 
           , aliases    = [] 
           , paliases   = [] 
           , embeds     = M.empty
           , qualifiers = []
           , decr       = []
           , lvars      = []
           , lazy       = S.empty
           , pragmas    = []
           , cmeasures  = []
           , imeasures  = []
           , classes    = []
           , termexprs  = []
           }

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
  first f s
    = s { measures   = first  f <$> (measures s)
        , asmSigs    = second f <$> (asmSigs s)
        , sigs       = second f <$> (sigs s)
        , localSigs  = second f <$> (localSigs s)
        , invariants = fmap   f <$> (invariants s)
        , ialiases   = fmapP  f <$> (ialiases s)
        , cmeasures  = first f  <$> (cmeasures s)
        , imeasures  = first f  <$> (imeasures s)
        , classes    = fmap f   <$> (classes s)
        }
    where fmapP f (x, y) = (fmap f x, fmap f y)

  second f s
    = s { measures   = fmap (second f) (measures s)
        , imeasures  = fmap (second f) (imeasures s)
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
defRefType (Def f dc xs body) = mkArrow as [] [] xts t'
  where 
    as  = RTV <$> dataConUnivTyVars dc
    xts = safeZip msg xs $ ofType `fmap` dataConOrigArgTys dc
    t'  = refineWithCtorBody dc f body t 
    t   = ofType $ dataConOrigResTy dc
    msg = "defRefType dc = " ++ showPpr dc 


refineWithCtorBody dc f body t =
  case stripRTypeBase t of 
    Just (Reft (v, _)) ->
      strengthen t $ Reft (v, [RConc $ bodyPred (EApp f [eVar v]) body])
    Nothing -> 
      errorstar $ "measure mismatch " ++ showpp f ++ " on con " ++ showPpr dc


bodyPred ::  Expr -> Body -> Pred
bodyPred fv (E e)    = PAtom Eq fv e
bodyPred fv (P p)    = PIff  (PBexp fv) p 
bodyPred fv (R v' p) = subst1 p (v', fv)


