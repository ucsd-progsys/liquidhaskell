{-# LANGUAGE DeriveAnyClass #-}
-- | This module contains the top-level structures that hold 
--   information about specifications.

{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}

module Language.Haskell.Liquid.Types.Specs (
  -- * Different types of specifications
  -- $differentSpecTypes
  -- * TargetInfo
  -- $targetInfo
    TargetInfo(..)
  -- * Gathering information about a module
  , TargetSrc(..)
  -- * TargetSpec
  -- $targetSpec
  , TargetSpec(..)
  -- * BareSpec
  -- $bareSpec
  , BareSpec(..)
  -- * LiftedSpec
  -- $liftedSpec
  , LiftedSpec(..)
  -- * Tracking dependencies
  -- $trackingDeps
  , TargetDependencies(..)
  , dropDependency
  -- * Predicates on spec types
  -- $predicates
  , isPLEVar
  , isExportedVar
  -- * Other types
  , QImports(..)
  , Spec(..)
  , GhcSpecVars(..)
  , GhcSpecSig(..)
  , GhcSpecNames(..)
  , GhcSpecTerm(..)
  , GhcSpecRefl(..)
  , GhcSpecLaws(..)
  , GhcSpecData(..)
  , GhcSpecQual(..)
  , BareDef
  , BareMeasure
  , SpecMeasure
  , VarOrLocSymbol
  , LawInstance(..)
  -- * Legacy data structures
  -- $legacyDataStructures
  , GhcSrc(..)
  , GhcSpec(..)
  -- * Provisional compatibility exports & optics
  -- $provisionalBackCompat
  , targetSrcIso
  , targetSpecGetter
  , bareSpecIso
  , liftedSpecGetter
  , unsafeFromLiftedSpec
  , emptyLiftedSpec
  ) where

import           Optics
import           GHC.Generics            hiding (to, moduleName)
import           Data.Binary
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Misc (sortNub)
import           Data.Hashable
import qualified Data.HashSet            as S
import           Data.HashSet            (HashSet)
import qualified Data.HashMap.Strict     as M
import           Data.HashMap.Strict     (HashMap)
import           Language.Haskell.Liquid.Types.Types 
import           Language.Haskell.Liquid.Types.Generics
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds 
import           Language.Haskell.Liquid.GHC.API hiding (text, (<+>))
import           Language.Haskell.Liquid.GHC.Types
import           Text.PrettyPrint.HughesPJ              (text, (<+>))


{- $differentSpecTypes

There are different types or \"flavours\" for a specification, depending on its lifecycle. The main goal
is always the same, i.e. refining the Haskell types and produce a final statement (i.e. safe or unsafe)
about the input program. In order to do so, a /specification/ is transformed in the way described by this
picture:

@
    +---------------+                                +-------------------+
    |   BareSpec    |                                |                   |  checked by liquid/liquidOne
    |               |                    ------------|    TargetSpec     |----------------------------- ..
    |(input module) |                   /            |                   |
    +---------------+  makeTargetSpec  /             +-------------------+
           +         -----------------/
    +---------------+                 \\              +-------------------+
    | {LiftedSpec}  |                  \\             |                   |    serialised on disk
    |               |                   -------------|    LiftedSpec     |----------------------------- ..
    |(dependencies) |                                |                   |
    +---------------+                                +-------------------+
          ^                                                    |
          |                   used-as                          |
          +----------------------------------------------------+
@

More specifically, we distinguish:

* 'BareSpec' - is the specification obtained by parsing the Liquid annotations of the input Haskell file.
  It typically contains information about the associated input Haskell module, with the exceptions of
  /assumptions/ that can refer to functions defined in other modules.

* 'LiftedSpec' - is the specification we obtain by \"lifting\" the 'BareSpec'. Most importantly, a
  'LiftedSpec' gets serialised on disk and becomes a /dependency/ for the verification of other 'BareSpec's.

   Lifting in this context consist of:

    1. Perform name-resolution (e.g. make all the relevant GHC's 'Var's qualified, resolve GHC's 'Name's, etc);
    2. Strip the final 'LiftedSpec' with information which are relevant (read: local) to just the input
       'BareSpec'. An example would be /local signatures/, used to annotate internal, auxiliary functions
       within a 'Module';
    3. Strip termination checks, which are /required/ (if specified) for a 'BareSpec' but not for the
       'LiftedSpec'.

* 'TargetSpec' - is the specification we /actually use for refinement/, and is conceptually an
  \"augmented\" 'BareSpec'. You can create a 'TargetSpec' by calling 'makeTargetSpec'.

In order to produce these spec types we have to gather information about the module being compiled by using
the GHC API and retain enough context of the compiled 'Module' in order to be able to construct the types
introduced aboves. The rest of this module introduced also these intermediate structures.
-}

-- $targetInfo 
-- The following is the overall type for /specifications/ obtained from
-- parsing the target source and dependent libraries. 
-- /IMPORTANT/: A 'TargetInfo' is what is /checked/ by LH itself and it /NEVER/ contains the 'LiftedSpec', 
-- because the checking happens only on the 'BareSpec' of the target module.
data TargetInfo = TargetInfo
  { giSrc  :: !TargetSrc
    -- ^ The 'TargetSrc' of the module being checked.
  , giSpec :: !TargetSpec 
    -- ^ The 'TargetSpec' of the module being checked.
  }

instance HasConfig TargetInfo where
  getConfig = getConfig . giSpec

-- | The 'TargetSrc' type is a collection of all the things we know about a module being currently
-- checked. It include things like the name of the module, the list of 'CoreBind's,
-- the 'TyCon's declared in this module (that includes 'TyCon's for classes), typeclass instances
-- and so and so forth. It might be consider a sort of 'ModGuts' embellished with LH-specific
-- information (for example, 'giDefVars' are populated with datacons from the module plus the
-- let vars derived from the A-normalisation).
data TargetSrc = TargetSrc
  { giIncDir    :: !FilePath              -- ^ Path for LH include/prelude directory
  , giTarget    :: !FilePath              -- ^ Source file for module
  , giTargetMod :: !ModName               -- ^ Name for module
  , giCbs       :: ![CoreBind]            -- ^ Source Code
  , gsTcs       :: ![TyCon]               -- ^ All used Type constructors
  , gsCls       :: !(Maybe [ClsInst])     -- ^ Class instances?
  , giDerVars   :: !(HashSet Var)         -- ^ Binders created by GHC eg dictionaries
  , giImpVars   :: ![Var]                 -- ^ Binders that are _read_ in module (but not defined?)
  , giDefVars   :: ![Var]                 -- ^ (Top-level) binders that are _defined_ in module
  , giUseVars   :: ![Var]                 -- ^ Binders that are _read_ in module
  , gsExports   :: !(HashSet StableName)  -- ^ `Name`s exported by the module being verified
  , gsFiTcs     :: ![TyCon]               -- ^ Family instance TyCons 
  , gsFiDcs     :: ![(F.Symbol, DataCon)] -- ^ Family instance DataCons 
  , gsPrimTcs   :: ![TyCon]               -- ^ Primitive GHC TyCons (from TysPrim.primTyCons)
  , gsQualImps  :: !QImports              -- ^ Map of qualified imports
  , gsAllImps   :: !(HashSet F.Symbol)    -- ^ Set of _all_ imported modules
  , gsTyThings  :: ![TyThing]             -- ^ All the @TyThing@s known to GHC
  }

-- | 'QImports' is a map of qualified imports.
data QImports = QImports 
  { qiModules :: !(S.HashSet F.Symbol)            -- ^ All the modules that are imported qualified
  , qiNames   :: !(M.HashMap F.Symbol [F.Symbol]) -- ^ Map from qualification to full module name
  } deriving Show

-- $targetSpec

-- | A 'TargetSpec' is what we /actually check via LiquidHaskell/. It is created as part of 'mkTargetSpec' 
-- alongside the 'LiftedSpec'. It shares a similar structure with a 'BareSpec', but manipulates and
-- transforms the data in preparation to the checking process.
data TargetSpec = TargetSpec
  { gsSig    :: !GhcSpecSig
  , gsQual   :: !GhcSpecQual
  , gsData   :: !GhcSpecData
  , gsName   :: !GhcSpecNames
  , gsVars   :: !GhcSpecVars
  , gsTerm   :: !GhcSpecTerm
  , gsRefl   :: !GhcSpecRefl
  , gsLaws   :: !GhcSpecLaws
  , gsImps   :: ![(F.Symbol, F.Sort)]  -- ^ Imported Environment
  , gsConfig :: !Config
  }

instance HasConfig TargetSpec where
  getConfig = gsConfig

-- | The collection of GHC 'Var's that a 'TargetSpec' needs to verify (or skip).
data GhcSpecVars = SpVar 
  { gsTgtVars    :: ![Var]                        -- ^ Top-level Binders To Verify (empty means ALL binders)
  , gsIgnoreVars :: !(S.HashSet Var)              -- ^ Top-level Binders To NOT Verify (empty means ALL binders)
  , gsLvars      :: !(S.HashSet Var)              -- ^ Variables that should be checked "lazily" in the environment they are used
  , gsCMethods   :: ![Var]                        -- ^ Refined Class methods 
  }

instance Semigroup GhcSpecVars where
  sv1 <> sv2 = SpVar 
    { gsTgtVars    = gsTgtVars    sv1 <> gsTgtVars    sv2
    , gsIgnoreVars = gsIgnoreVars sv1 <> gsIgnoreVars sv2
    , gsLvars      = gsLvars      sv1 <> gsLvars      sv2
    , gsCMethods   = gsCMethods   sv1 <> gsCMethods   sv2
    }

instance Monoid GhcSpecVars where
  mempty = SpVar mempty mempty mempty mempty

data GhcSpecQual = SpQual 
  { gsQualifiers :: ![F.Qualifier]                -- ^ Qualifiers in Source/Spec files e.g tests/pos/qualTest.hs
  , gsRTAliases  :: ![F.Located SpecRTAlias]      -- ^ Refinement type aliases (only used for qualifiers)
  }

data GhcSpecSig = SpSig 
  { gsTySigs   :: ![(Var, LocSpecType)]           -- ^ Asserted Reftypes
  , gsAsmSigs  :: ![(Var, LocSpecType)]           -- ^ Assumed Reftypes
  , gsRefSigs  :: ![(Var, LocSpecType)]           -- ^ Reflected Reftypes 
  , gsInSigs   :: ![(Var, LocSpecType)]           -- ^ Auto generated Signatures
  , gsNewTypes :: ![(TyCon, LocSpecType)]         -- ^ Mapping of 'newtype' type constructors with their refined types.
  , gsDicts    :: !(DEnv Var LocSpecType)            -- ^ Refined Classes from Instances 
  , gsMethods  :: ![(Var, MethodType LocSpecType)]   -- ^ Refined Classes from Classes 
  , gsTexprs   :: ![(Var, LocSpecType, [F.Located F.Expr])]  -- ^ Lexicographically ordered expressions for termination
  }

instance Semigroup GhcSpecSig where
  x <> y = SpSig 
    { gsTySigs   = gsTySigs x   <> gsTySigs y   
    , gsAsmSigs  = gsAsmSigs x  <> gsAsmSigs y   
    , gsRefSigs  = gsRefSigs x  <> gsRefSigs y   
    , gsInSigs   = gsInSigs x   <> gsInSigs y   
    , gsNewTypes = gsNewTypes x <> gsNewTypes y   
    , gsDicts    = gsDicts x    <> gsDicts y   
    , gsMethods  = gsMethods x  <> gsMethods y   
    , gsTexprs   = gsTexprs x   <> gsTexprs y   

    }







instance Monoid GhcSpecSig where
  mempty = SpSig mempty mempty mempty mempty mempty mempty mempty mempty  

data GhcSpecData = SpData 
  { gsCtors      :: ![(Var, LocSpecType)]         -- ^ Data Constructor Measure Sigs
  , gsMeas       :: ![(F.Symbol, LocSpecType)]    -- ^ Measure Types eg.  len :: [a] -> Int
  , gsInvariants :: ![(Maybe Var, LocSpecType)]   -- ^ Data type invariants from measure definitions, e.g forall a. {v: [a] | len(v) >= 0}
  , gsIaliases   :: ![(LocSpecType, LocSpecType)] -- ^ Data type invariant aliases 
  , gsMeasures   :: ![Measure SpecType DataCon]   -- ^ Measure definitions
  , gsUnsorted   :: ![UnSortedExpr]
  }
data GhcSpecNames = SpNames 
  { gsFreeSyms   :: ![(F.Symbol, Var)]            -- ^ List of `Symbol` free in spec and corresponding GHC var, eg. (Cons, Cons#7uz) from tests/pos/ex1.hs
  , gsDconsP     :: ![F.Located DataCon]          -- ^ Predicated Data-Constructors, e.g. see tests/pos/Map.hs
  , gsTconsP     :: ![TyConP]                     -- ^ Predicated Type-Constructors, e.g. see tests/pos/Map.hs
  , gsTcEmbeds   :: !(F.TCEmb TyCon)              -- ^ Embedding GHC Tycons into fixpoint sorts e.g. "embed Set as Set_set" from include/Data/Set.spec
  , gsADTs       :: ![F.DataDecl]                 -- ^ ADTs extracted from Haskell 'data' definitions
  , gsTyconEnv   :: !TyConMap
  }

data GhcSpecTerm = SpTerm 
  { gsStTerm     :: !(S.HashSet Var)              -- ^ Binders to CHECK by structural termination
  , gsAutosize   :: !(S.HashSet TyCon)            -- ^ Binders to IGNORE during termination checking
  , gsLazy       :: !(S.HashSet Var)              -- ^ Binders to IGNORE during termination checking
  , gsFail       :: !(S.HashSet (F.Located Var))    -- ^ Binders to fail type checking
  , gsDecr       :: ![(Var, [Int])]               -- ^ Lexicographic order of decreasing args (DEPRECATED) 
  , gsNonStTerm  :: !(S.HashSet Var)              -- ^ Binders to CHECK using REFINEMENT-TYPES/termination metrics 
  }

instance Semigroup GhcSpecTerm where
  t1 <> t2 = SpTerm
    { gsStTerm    = gsStTerm t1    <> gsStTerm t2
    , gsAutosize  = gsAutosize t1  <> gsAutosize t2
    , gsLazy      = gsLazy t1      <> gsLazy t2
    , gsFail      = gsFail t1      <> gsFail t2
    , gsDecr      = gsDecr t1      <> gsDecr t2
    , gsNonStTerm = gsNonStTerm t1 <> gsNonStTerm t2
    }

instance Monoid GhcSpecTerm where
  mempty = SpTerm mempty mempty mempty mempty mempty mempty
data GhcSpecRefl = SpRefl 
  { gsAutoInst     :: !(M.HashMap Var (Maybe Int))      -- ^ Binders to USE PLE 
  , gsHAxioms      :: ![(Var, LocSpecType, F.Equation)] -- ^ Lifted definitions 
  , gsImpAxioms    :: ![F.Equation]                     -- ^ Axioms from imported reflected functions
  , gsMyAxioms     :: ![F.Equation]                     -- ^ Axioms from my reflected functions
  , gsReflects     :: ![Var]                            -- ^ Binders for reflected functions
  , gsLogicMap     :: !LogicMap
  , gsWiredReft    :: ![Var]
  , gsRewrites     :: S.HashSet (F.Located Var)
  , gsRewritesWith :: M.HashMap Var [Var]
  }

instance Semigroup GhcSpecRefl where
  x <> y = SpRefl 
    { gsAutoInst = gsAutoInst x <> gsAutoInst y 
    , gsHAxioms  = gsHAxioms x <> gsHAxioms y
    , gsImpAxioms = gsImpAxioms x <> gsImpAxioms y
    , gsMyAxioms = gsMyAxioms x <> gsMyAxioms y
    , gsReflects = gsReflects x <> gsReflects y
    , gsLogicMap = gsLogicMap x <> gsLogicMap y
    , gsWiredReft = gsWiredReft x <> gsWiredReft y
    , gsRewrites = gsRewrites x <> gsRewrites y
    , gsRewritesWith = gsRewritesWith x <> gsRewritesWith y
    } 

instance Monoid GhcSpecRefl where
  mempty = SpRefl mempty mempty mempty
                  mempty mempty mempty
                  mempty mempty mempty
data GhcSpecLaws = SpLaws 
  { gsLawDefs :: !([(Class, [(Var, LocSpecType)])])
  , gsLawInst :: ![LawInstance]
  }

data LawInstance = LawInstance
  { lilName   :: Class
  , liSupers  :: [LocSpecType]
  , lilTyArgs :: [LocSpecType]
  , lilEqus   :: [(VarOrLocSymbol, (VarOrLocSymbol, Maybe LocSpecType))]
  , lilPos    :: SrcSpan
  }  

type VarOrLocSymbol = Either Var LocSymbol
type BareMeasure   = Measure LocBareType F.LocSymbol
type BareDef       = Def     LocBareType F.LocSymbol
type SpecMeasure   = Measure LocSpecType DataCon

-- $bareSpec

-- | A 'BareSpec' is the spec we derive by parsing the Liquid Haskell annotations of a single file. As
-- such, it contains things which are relevant for validation and lifting; it contains things like
-- the pragmas the user defined, the termination condition (if termination-checking is enabled) and so
-- on and so forth. /Crucially/, as a 'BareSpec' is still subject to \"preflight checks\", it may contain
-- duplicates (e.g. duplicate measures, duplicate type declarations etc.) and therefore most of the fields
-- for a 'BareSpec' are lists, so that we can report these errors to the end user: it would be an error
-- to silently ignore the duplication and leave the duplicate resolution to whichever 'Eq' instance is
-- implemented for the relevant field.
--
-- Also, a 'BareSpec' has not yet been subject to name resolution, so it may refer
-- to undefined or out-of-scope entities.
newtype BareSpec =
  MkBareSpec { getBareSpec :: Spec LocBareType F.LocSymbol }
  deriving (Generic, Show, Binary)

instance Semigroup BareSpec where
  x <> y = MkBareSpec { getBareSpec = getBareSpec x <> getBareSpec y }

instance Monoid BareSpec where
  mempty = MkBareSpec { getBareSpec = mempty } 


-- instance Semigroup (Spec ty bndr) where

-- | A generic 'Spec' type, polymorphic over the inner choice of type and binder.
data Spec ty bndr  = Spec
  { measures   :: ![Measure ty bndr]              -- ^ User-defined properties for ADTs
  , impSigs    :: ![(F.Symbol, F.Sort)]           -- ^ Imported variables types
  , expSigs    :: ![(F.Symbol, F.Sort)]           -- ^ Exported variables types
  , asmSigs    :: ![(F.LocSymbol, ty)]            -- ^ Assumed (unchecked) types; including reflected signatures
  , sigs       :: ![(F.LocSymbol, ty)]            -- ^ Imported functions and types
  , localSigs  :: ![(F.LocSymbol, ty)]            -- ^ Local type signatures
  , reflSigs   :: ![(F.LocSymbol, ty)]            -- ^ Reflected type signatures
  , invariants :: ![(Maybe F.LocSymbol, ty)]      -- ^ Data type invariants; the Maybe is the generating measure
  , ialiases   :: ![(ty, ty)]                     -- ^ Data type invariants to be checked
  , imports    :: ![F.Symbol]                     -- ^ Loaded spec module names
  , dataDecls  :: ![DataDecl]                     -- ^ Predicated data definitions
  , newtyDecls :: ![DataDecl]                     -- ^ Predicated new type definitions
  , includes   :: ![FilePath]                     -- ^ Included qualifier files
  , aliases    :: ![F.Located (RTAlias F.Symbol BareType)] -- ^ RefType aliases
  , ealiases   :: ![F.Located (RTAlias F.Symbol F.Expr)]   -- ^ Expression aliases
  , embeds     :: !(F.TCEmb F.LocSymbol)                   -- ^ GHC-Tycon-to-fixpoint Tycon map
  , qualifiers :: ![F.Qualifier]                           -- ^ Qualifiers in source/spec files
  , decr       :: ![(F.LocSymbol, [Int])]         -- ^ Information on decreasing arguments
  , lvars      :: !(S.HashSet F.LocSymbol)        -- ^ Variables that should be checked in the environment they are used
  , lazy       :: !(S.HashSet F.LocSymbol)        -- ^ Ignore Termination Check in these Functions
  , rewrites    :: !(S.HashSet F.LocSymbol)        -- ^ Theorems turned into rewrite rules 
  , rewriteWith :: !(M.HashMap F.LocSymbol [F.LocSymbol]) -- ^ Definitions using rewrite rules
  , fails      :: !(S.HashSet F.LocSymbol)        -- ^ These Functions should be unsafe
  , reflects   :: !(S.HashSet F.LocSymbol)        -- ^ Binders to reflect
  , autois     :: !(M.HashMap F.LocSymbol (Maybe Int))  -- ^ Automatically instantiate axioms in these Functions with maybe specified fuel
  , hmeas      :: !(S.HashSet F.LocSymbol)        -- ^ Binders to turn into measures using haskell definitions
  , hbounds    :: !(S.HashSet F.LocSymbol)        -- ^ Binders to turn into bounds using haskell definitions
  , inlines    :: !(S.HashSet F.LocSymbol)        -- ^ Binders to turn into logic inline using haskell definitions
  , ignores    :: !(S.HashSet F.LocSymbol)        -- ^ Binders to ignore during checking; that is DON't check the corebind. 
  , autosize   :: !(S.HashSet F.LocSymbol)        -- ^ Type Constructors that get automatically sizing info
  , pragmas    :: ![F.Located String]             -- ^ Command-line configurations passed in through source
  , cmeasures  :: ![Measure ty ()]                -- ^ Measures attached to a type-class
  , imeasures  :: ![Measure ty bndr]              -- ^ Mappings from (measure,type) -> measure
  , classes    :: ![RClass ty]                    -- ^ Refined Type-Classes
  , claws      :: ![RClass ty]                    -- ^ Refined Type-Classe Laws
  , termexprs  :: ![(F.LocSymbol, [F.Located F.Expr])] -- ^ Terminating Conditions for functions
  , rinstance  :: ![RInstance ty]
  , ilaws      :: ![RILaws ty]
  , dvariance  :: ![(F.LocSymbol, [Variance])]         -- ^ ? Where do these come from ?!
  , bounds     :: !(RRBEnv ty)
  , defs       :: !(M.HashMap F.LocSymbol F.Symbol)    -- ^ Temporary (?) hack to deal with dictionaries in specifications
                                                       --   see tests/pos/NatClass.hs
  , axeqs      :: ![F.Equation]                        -- ^ Equalities used for Proof-By-Evaluation
  } deriving (Generic, Show)

instance Binary (Spec LocBareType F.LocSymbol)

instance (Show ty, Show bndr, F.PPrint ty, F.PPrint bndr) => F.PPrint (Spec ty bndr) where
    pprintTidy k sp = text "dataDecls = " <+> pprintTidy k  (dataDecls sp)

-- /NOTA BENE/: These instances below are considered legacy, because merging two 'Spec's together doesn't
-- really make sense, and we provide this only for legacy purposes.
instance Semigroup (Spec ty bndr) where
  s1 <> s2
    = Spec { measures   =           measures   s1 ++ measures   s2
           , impSigs    =           impSigs    s1 ++ impSigs    s2
           , expSigs    =           expSigs    s1 ++ expSigs    s2 
           , asmSigs    =           asmSigs    s1 ++ asmSigs    s2
           , sigs       =           sigs       s1 ++ sigs       s2
           , localSigs  =           localSigs  s1 ++ localSigs  s2
           , reflSigs   =           reflSigs   s1 ++ reflSigs   s2
           , invariants =           invariants s1 ++ invariants s2
           , ialiases   =           ialiases   s1 ++ ialiases   s2
           , imports    = sortNub $ imports    s1 ++ imports    s2
           , dataDecls  =           dataDecls  s1 ++ dataDecls  s2
           , newtyDecls =           newtyDecls s1 ++ newtyDecls s2
           , includes   = sortNub $ includes   s1 ++ includes   s2
           , aliases    =           aliases    s1 ++ aliases    s2
           , ealiases   =           ealiases   s1 ++ ealiases   s2
           , qualifiers =           qualifiers s1 ++ qualifiers s2
           , decr       =           decr       s1 ++ decr       s2
           , pragmas    =           pragmas    s1 ++ pragmas    s2
           , cmeasures  =           cmeasures  s1 ++ cmeasures  s2
           , imeasures  =           imeasures  s1 ++ imeasures  s2
           , classes    =           classes    s1 ++ classes    s2
           , claws      =           claws      s1 ++ claws      s2
           , termexprs  =           termexprs  s1 ++ termexprs  s2
           , rinstance  =           rinstance  s1 ++ rinstance  s2
           , ilaws      =               ilaws  s1 ++ ilaws      s2 
           , dvariance  =           dvariance  s1 ++ dvariance  s2
           , axeqs      =           axeqs s1      ++ axeqs s2
           , embeds     = mappend   (embeds   s1)  (embeds   s2)
           , lvars      = S.union   (lvars    s1)  (lvars    s2)
           , lazy       = S.union   (lazy     s1)  (lazy     s2)
           , rewrites   = S.union   (rewrites    s1)  (rewrites    s2)
           , rewriteWith = M.union  (rewriteWith s1)  (rewriteWith s2)
           , fails      = S.union   (fails    s1)  (fails    s2)
           , reflects   = S.union   (reflects s1)  (reflects s2)
           , hmeas      = S.union   (hmeas    s1)  (hmeas    s2)
           , hbounds    = S.union   (hbounds  s1)  (hbounds  s2)
           , inlines    = S.union   (inlines  s1)  (inlines  s2)
           , ignores    = S.union   (ignores  s1)  (ignores  s2)
           , autosize   = S.union   (autosize s1)  (autosize s2)
           , bounds     = M.union   (bounds   s1)  (bounds   s2)
           , defs       = M.union   (defs     s1)  (defs     s2)
           , autois     = M.union   (autois s1)      (autois s2)
           }

instance Monoid (Spec ty bndr) where
  mappend = (<>)
  mempty
    = Spec { measures   = []
           , impSigs    = [] 
           , expSigs    = [] 
           , asmSigs    = []
           , sigs       = []
           , localSigs  = []
           , reflSigs   = []
           , invariants = []
           , ialiases   = []
           , imports    = []
           , dataDecls  = []
           , newtyDecls = []
           , includes   = []
           , aliases    = []
           , ealiases   = []
           , embeds     = mempty
           , qualifiers = []
           , decr       = []
           , lvars      = S.empty 
           , lazy       = S.empty
           , rewrites   = S.empty
           , rewriteWith = M.empty
           , fails      = S.empty
           , autois     = M.empty
           , hmeas      = S.empty
           , reflects   = S.empty
           , hbounds    = S.empty
           , inlines    = S.empty
           , ignores    = S.empty
           , autosize   = S.empty
           , pragmas    = []
           , cmeasures  = []
           , imeasures  = []
           , classes    = []
           , claws      = [] 
           , termexprs  = []
           , rinstance  = []
           , ilaws      = [] 
           , dvariance  = []
           , axeqs      = []
           , bounds     = M.empty
           , defs       = M.empty
           }

-- $liftedSpec

-- | A 'LiftedSpec' is derived from an input 'BareSpec' and a set of its dependencies.
-- The general motivations for lifting a spec are (a) name resolution, (b) the fact that some info is
-- only relevant for checking the body of functions but does not need to be exported, e.g. 
-- termination measures, or the fact that a type signature was assumed.
-- A 'LiftedSpec' is /what we serialise on disk and what the clients should will be using/.
--
-- What we /do not/ have compared to a 'BareSpec':
--
-- * The 'localSigs', as it's not necessary/visible to clients;
-- * The 'includes', as they are probably not reachable for clients anyway;
-- * The 'reflSigs', they are now just \"normal\" signatures;
-- * The 'lazy', we don't do termination checking in lifted specs;
-- * The 'reflects', the reflection has already happened at this point;
-- * The 'hmeas', we have /already/ turned these into measures at this point;
-- * The 'hbounds', ditto as 'hmeas';
-- * The 'inlines', ditto as 'hmeas';
-- * The 'ignores', ditto as 'hmeas';
-- * The 'pragmas', we can't make any use of this information for lifted specs;
-- * The 'termexprs', we don't do termination checking in lifted specs;
--
-- Apart from less fields, a 'LiftedSpec' /replaces all instances of lists with sets/, to enforce
-- duplicate detection and removal on what we serialise on disk.
data LiftedSpec = LiftedSpec
  { liftedMeasures   :: HashSet (Measure LocBareType F.LocSymbol)
    -- ^ User-defined properties for ADTs
  , liftedImpSigs    :: HashSet (F.Symbol, F.Sort)
    -- ^ Imported variables types
  , liftedExpSigs    :: HashSet (F.Symbol, F.Sort)
    -- ^ Exported variables types
  , liftedAsmSigs    :: HashSet (F.LocSymbol, LocBareType)
    -- ^ Assumed (unchecked) types; including reflected signatures
  , liftedSigs       :: HashSet (F.LocSymbol, LocBareType)
    -- ^ Imported functions and types
  , liftedInvariants :: HashSet (Maybe F.LocSymbol, LocBareType)
    -- ^ Data type invariants; the Maybe is the generating measure
  , liftedIaliases   :: HashSet (LocBareType, LocBareType)
    -- ^ Data type invariants to be checked
  , liftedImports    :: HashSet F.Symbol
    -- ^ Loaded spec module names
  , liftedDataDecls  :: HashSet DataDecl
    -- ^ Predicated data definitions
  , liftedNewtyDecls :: HashSet DataDecl
    -- ^ Predicated new type definitions
  , liftedAliases    :: HashSet (F.Located (RTAlias F.Symbol BareType))
    -- ^ RefType aliases
  , liftedEaliases   :: HashSet (F.Located (RTAlias F.Symbol F.Expr))
    -- ^ Expression aliases
  , liftedEmbeds     :: F.TCEmb F.LocSymbol
    -- ^ GHC-Tycon-to-fixpoint Tycon map
  , liftedQualifiers :: HashSet F.Qualifier
    -- ^ Qualifiers in source/spec files
  , liftedDecr       :: HashSet (F.LocSymbol, [Int])
    -- ^ Information on decreasing arguments
  , liftedLvars      :: HashSet F.LocSymbol
    -- ^ Variables that should be checked in the environment they are used
  , liftedAutois     :: M.HashMap F.LocSymbol (Maybe Int)
    -- ^ Automatically instantiate axioms in these Functions with maybe specified fuel
  , liftedAutosize   :: HashSet F.LocSymbol
    -- ^ Type Constructors that get automatically sizing info
  , liftedCmeasures  :: HashSet (Measure LocBareType ())
    -- ^ Measures attached to a type-class
  , liftedImeasures  :: HashSet (Measure LocBareType F.LocSymbol)
    -- ^ Mappings from (measure,type) -> measure
  , liftedClasses    :: HashSet (RClass LocBareType)
    -- ^ Refined Type-Classes
  , liftedClaws      :: HashSet (RClass LocBareType)
    -- ^ Refined Type-Classe Laws
  , liftedRinstance  :: HashSet (RInstance LocBareType)
  , liftedIlaws      :: HashSet (RILaws LocBareType)
  , liftedDvariance  :: HashSet (F.LocSymbol, [Variance])
    -- ^ ? Where do these come from ?!
  , liftedBounds     :: RRBEnv LocBareType
  , liftedDefs       :: M.HashMap F.LocSymbol F.Symbol
    -- ^ Temporary (?) hack to deal with dictionaries in specifications
    --   see tests/pos/NatClass.hs
  , liftedAxeqs      :: HashSet F.Equation
    -- ^ Equalities used for Proof-By-Evaluation
  } deriving (Eq, Generic, Show)
    deriving Hashable via Generically LiftedSpec 
    deriving Binary   via Generically LiftedSpec 

instance Binary F.Equation 

emptyLiftedSpec :: LiftedSpec
emptyLiftedSpec = LiftedSpec
  { liftedMeasures = mempty 
  , liftedImpSigs  = mempty
  , liftedExpSigs  = mempty
  , liftedAsmSigs  = mempty
  , liftedSigs     = mempty
  , liftedInvariants = mempty
  , liftedIaliases   = mempty
  , liftedImports    = mempty
  , liftedDataDecls  = mempty
  , liftedNewtyDecls = mempty
  , liftedAliases    = mempty
  , liftedEaliases   = mempty
  , liftedEmbeds     = mempty
  , liftedQualifiers = mempty
  , liftedDecr       = mempty
  , liftedLvars      = mempty
  , liftedAutois     = mempty
  , liftedAutosize   = mempty
  , liftedCmeasures  = mempty
  , liftedImeasures  = mempty
  , liftedClasses    = mempty
  , liftedClaws      = mempty
  , liftedRinstance  = mempty
  , liftedIlaws      = mempty
  , liftedDvariance  = mempty
  , liftedBounds     = mempty
  , liftedDefs       = mempty
  , liftedAxeqs      = mempty
  }

-- $trackingDeps

-- | The /target/ dependencies that concur to the creation of a 'TargetSpec' and a 'LiftedSpec'.
newtype TargetDependencies =
  TargetDependencies { getDependencies :: HashMap StableModule LiftedSpec }
  deriving (Eq, Show, Generic)
  deriving Binary via Generically TargetDependencies

-- instance S.Store TargetDependencies

instance Semigroup TargetDependencies where
  x <> y = TargetDependencies 
             { getDependencies = getDependencies x <> getDependencies y 
             }


instance Monoid TargetDependencies where
  mempty = TargetDependencies mempty

-- | Drop the given 'StableModule' from the dependencies.
dropDependency :: StableModule -> TargetDependencies -> TargetDependencies
dropDependency sm (TargetDependencies deps) = TargetDependencies (M.delete sm deps)

-- $predicates

-- | Returns 'True' if the input 'Var' is a /PLE/ one.
isPLEVar :: TargetSpec -> Var -> Bool 
isPLEVar sp x = M.member x (gsAutoInst (gsRefl sp)) 

-- | Returns 'True' if the input 'Var' was exported in the module the input 'TargetSrc' represents.
isExportedVar :: TargetSrc -> Var -> Bool
isExportedVar src v = mkStableName n `S.member` ns
  where
    n                = getName v
    ns               = gsExports src

--
-- $legacyDataStructures
--
{- 
data GhcInfo = GI
  { _giSrc       :: !GhcSrc  
  , _giSpec      :: !GhcSpec               -- ^ All specification information for module
  }
-}

data GhcSrc = Src 
  { _giIncDir    :: !FilePath              -- ^ Path for LH include/prelude directory
  , _giTarget    :: !FilePath              -- ^ Source file for module
  , _giTargetMod :: !ModName               -- ^ Name for module
  , _giCbs       :: ![CoreBind]            -- ^ Source Code
  , _gsTcs       :: ![TyCon]               -- ^ All used Type constructors
  , _gsCls       :: !(Maybe [ClsInst])     -- ^ Class instances?
  , _giDerVars   :: !(S.HashSet Var)       -- ^ Binders created by GHC eg dictionaries
  , _giImpVars   :: ![Var]                 -- ^ Binders that are _read_ in module (but not defined?)
  , _giDefVars   :: ![Var]                 -- ^ (Top-level) binders that are _defined_ in module
  , _giUseVars   :: ![Var]                 -- ^ Binders that are _read_ in module
  , _gsExports   :: !(HashSet StableName)  -- ^ `Name`s exported by the module being verified
  , _gsFiTcs     :: ![TyCon]               -- ^ Family instance TyCons 
  , _gsFiDcs     :: ![(F.Symbol, DataCon)] -- ^ Family instance DataCons 
  , _gsPrimTcs   :: ![TyCon]               -- ^ Primitive GHC TyCons (from TysPrim.primTyCons)
  , _gsQualImps  :: !QImports              -- ^ Map of qualified imports
  , _gsAllImps   :: !(S.HashSet F.Symbol)  -- ^ Set of _all_ imported modules
  , _gsTyThings  :: ![TyThing]             -- ^ All the @TyThing@s known to GHC
  }

data GhcSpec = SP 
  { _gsSig    :: !GhcSpecSig  
  , _gsQual   :: !GhcSpecQual 
  , _gsData   :: !GhcSpecData 
  , _gsName   :: !GhcSpecNames 
  , _gsVars   :: !GhcSpecVars 
  , _gsTerm   :: !GhcSpecTerm 
  , _gsRefl   :: !GhcSpecRefl   
  , _gsLaws   :: !GhcSpecLaws 
  , _gsImps   :: ![(F.Symbol, F.Sort)]  -- ^ Imported Environment
  , _gsConfig :: !Config
  , _gsLSpec  :: !(Spec LocBareType F.LocSymbol) -- ^ Lifted specification for the target module
  }

instance HasConfig GhcSpec where
  getConfig = _gsConfig


{- $provisionalBackCompat

In order to smooth out the migration process to this API, here we provide some /compat/ 'Iso' and 'Prism'
to convert from/to the old data structures, so that migration can be done organically over time.
-}

targetSrcIso :: Iso' GhcSrc TargetSrc
targetSrcIso = iso toTargetSrc fromTargetSrc
  where
    toTargetSrc a = TargetSrc
      { giIncDir    = _giIncDir a
      , giTarget    = _giTarget a
      , giTargetMod = _giTargetMod a
      , giCbs       = _giCbs a
      , gsTcs       = _gsTcs a
      , gsCls       = _gsCls a
      , giDerVars   = _giDerVars a
      , giImpVars   = _giImpVars a
      , giDefVars   = _giDefVars a
      , giUseVars   = _giUseVars a
      , gsExports   = _gsExports a
      , gsFiTcs     = _gsFiTcs a
      , gsFiDcs     = _gsFiDcs a
      , gsPrimTcs   = _gsPrimTcs a
      , gsQualImps  = _gsQualImps a
      , gsAllImps   = _gsAllImps a
      , gsTyThings  = _gsTyThings a
      }

    fromTargetSrc a = Src
      { _giIncDir    = giIncDir a
      , _giTarget    = giTarget a
      , _giTargetMod = giTargetMod a
      , _giCbs       = giCbs a
      , _gsTcs       = gsTcs a
      , _gsCls       = gsCls a
      , _giDerVars   = giDerVars a
      , _giImpVars   = giImpVars a
      , _giDefVars   = giDefVars a
      , _giUseVars   = giUseVars a
      , _gsExports   = gsExports a
      , _gsFiTcs     = gsFiTcs a
      , _gsFiDcs     = gsFiDcs a
      , _gsPrimTcs   = gsPrimTcs a
      , _gsQualImps  = gsQualImps a
      , _gsAllImps   = gsAllImps a
      , _gsTyThings  = gsTyThings a
      }

targetSpecGetter :: Getter GhcSpec (TargetSpec, LiftedSpec)
targetSpecGetter = 
  to (\ghcSpec -> (toTargetSpec ghcSpec, view (to _gsLSpec % liftedSpecGetter) ghcSpec))
  where
    toTargetSpec a = TargetSpec
      { gsSig    = _gsSig a
      , gsQual   = _gsQual a
      , gsData   = _gsData a
      , gsName   = _gsName a
      , gsVars   = _gsVars a
      , gsTerm   = _gsTerm a
      , gsRefl   = _gsRefl a
      , gsLaws   = _gsLaws a
      , gsImps   = _gsImps a
      , gsConfig = _gsConfig a
      }

bareSpecIso :: Iso' (Spec LocBareType F.LocSymbol) BareSpec
bareSpecIso = iso MkBareSpec getBareSpec

liftedSpecGetter :: Getter (Spec LocBareType F.LocSymbol) LiftedSpec
liftedSpecGetter = to toLiftedSpec
  where
    toLiftedSpec a = LiftedSpec 
      { liftedMeasures   = S.fromList . measures $ a
      , liftedImpSigs    = S.fromList . impSigs  $ a
      , liftedExpSigs    = S.fromList . expSigs  $ a
      , liftedAsmSigs    = S.fromList . asmSigs  $ a
      , liftedSigs       = S.fromList . sigs     $ a
      , liftedInvariants = S.fromList . invariants $ a
      , liftedIaliases   = S.fromList . ialiases $ a
      , liftedImports    = S.fromList . imports $ a
      , liftedDataDecls  = S.fromList . dataDecls $ a
      , liftedNewtyDecls = S.fromList . newtyDecls $ a
      , liftedAliases    = S.fromList . aliases $ a
      , liftedEaliases   = S.fromList . ealiases $ a
      , liftedEmbeds     = embeds a
      , liftedQualifiers = S.fromList . qualifiers $ a
      , liftedDecr       = S.fromList . decr $ a
      , liftedLvars      = lvars a
      , liftedAutois     = autois a
      , liftedAutosize   = autosize a
      , liftedCmeasures  = S.fromList . cmeasures $ a
      , liftedImeasures  = S.fromList . imeasures $ a
      , liftedClasses    = S.fromList . classes $ a
      , liftedClaws      = S.fromList . claws $ a
      , liftedRinstance  = S.fromList . rinstance $ a
      , liftedIlaws      = S.fromList . ilaws $ a
      , liftedDvariance  = S.fromList . dvariance $ a
      , liftedBounds     = bounds a
      , liftedDefs       = defs a
      , liftedAxeqs      = S.fromList . axeqs $ a
      }

-- This is a temporary internal function that we use to convert the input dependencies into a format
-- suitable for 'makeGhcSpec'.
unsafeFromLiftedSpec :: LiftedSpec -> Spec LocBareType F.LocSymbol
unsafeFromLiftedSpec a = Spec
  { measures   = S.toList . liftedMeasures $ a
  , impSigs    = S.toList . liftedImpSigs $ a
  , expSigs    = S.toList . liftedExpSigs $ a
  , asmSigs    = S.toList . liftedAsmSigs $ a
  , sigs       = S.toList . liftedSigs $ a
  , localSigs  = mempty
  , reflSigs   = mempty
  , invariants = S.toList . liftedInvariants $ a
  , ialiases   = S.toList . liftedIaliases $ a
  , imports    = S.toList . liftedImports $ a
  , dataDecls  = S.toList . liftedDataDecls $ a
  , newtyDecls = S.toList . liftedNewtyDecls $ a
  , includes   = mempty
  , aliases    = S.toList . liftedAliases $ a
  , ealiases   = S.toList . liftedEaliases $ a
  , embeds     = liftedEmbeds a
  , qualifiers = S.toList . liftedQualifiers $ a
  , decr       = S.toList . liftedDecr $ a
  , lvars      = liftedLvars a
  , lazy       = mempty
  , fails      = mempty
  , rewrites   = mempty
  , rewriteWith = mempty
  , reflects   = mempty
  , autois     = liftedAutois a
  , hmeas      = mempty
  , hbounds    = mempty
  , inlines    = mempty
  , ignores    = mempty
  , autosize   = liftedAutosize a
  , pragmas    = mempty
  , cmeasures  = S.toList . liftedCmeasures $ a
  , imeasures  = S.toList . liftedImeasures $ a
  , classes    = S.toList . liftedClasses $ a
  , claws      = S.toList . liftedClaws $ a
  , termexprs  = mempty
  , rinstance  = S.toList . liftedRinstance $ a
  , ilaws      = S.toList . liftedIlaws $ a
  , dvariance  = S.toList . liftedDvariance $ a
  , bounds     = liftedBounds a
  , defs       = liftedDefs a
  , axeqs      = S.toList . liftedAxeqs $ a
  }
