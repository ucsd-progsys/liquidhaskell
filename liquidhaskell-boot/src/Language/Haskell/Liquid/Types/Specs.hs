-- | This module contains the top-level structures that hold
--   information about specifications.

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wno-orphans #-}

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
  , BareSpec
  , BareSpecLHName
  , BareSpecParsed
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
  , GhcSpecData(..)
  , GhcSpecQual(..)
  , BareDef
  , BareMeasure
  , SpecMeasure
  , VarOrLocSymbol
  , emapSpecM
  , fromBareSpecLHName
  , fromBareSpecParsed
  , mapSpecLName
  , mapSpecTy
  -- * Legacy data structures
  -- $legacyDataStructures
  , GhcSrc(..)
  , GhcSpec(..)
  -- * Provisional compatibility exports & optics
  -- $provisionalBackCompat
  , toTargetSrc
  , fromTargetSrc
  , toTargetSpec
  , toLiftedSpec
  , unsafeFromLiftedSpec
  , emptyLiftedSpec
  ) where

import           GHC.Generics            hiding (to, moduleName)
import           Data.Bifunctor          (bimap, first)
import           Data.Bitraversable      (bimapM)
import           Data.Binary
import qualified Language.Fixpoint.Types as F
import           Data.Data (Data)
import           Data.Hashable
import qualified Data.HashSet            as S
import           Data.HashSet            (HashSet)
import qualified Data.HashMap.Lazy       as Lazy.M
import qualified Data.HashMap.Strict     as M
import           Data.HashMap.Strict     (HashMap)
import           Language.Haskell.Liquid.GHC.Misc (dropModuleNames)
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds
import           Language.Haskell.Liquid.UX.Config
import           Liquid.GHC.API hiding (Binary, text, (<+>), panic)
import           Language.Haskell.Liquid.GHC.Types
import           Text.PrettyPrint.HughesPJ              (text, (<+>))
import           Text.PrettyPrint.HughesPJ as HughesPJ (($$))


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
  { giTarget    :: !FilePath              -- ^ Source file for module
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
  , gsImps   :: ![(F.Symbol, F.Sort)]  -- ^ Imported Environment
  , gsConfig :: !Config
  }
  deriving Show

instance HasConfig TargetSpec where
  getConfig = gsConfig

-- | The collection of GHC 'Var's that a 'TargetSpec' needs to verify (or skip).
data GhcSpecVars = SpVar
  { gsTgtVars    :: ![Var]                        -- ^ Top-level Binders To Verify (empty means ALL binders)
  , gsIgnoreVars :: !(S.HashSet Var)              -- ^ Top-level Binders To NOT Verify (empty means ALL binders)
  , gsLvars      :: !(S.HashSet Var)              -- ^ Variables that should be checked "lazily" in the environment they are used
  , gsCMethods   :: ![Var]                        -- ^ Refined Class methods
  }
  deriving Show

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
  deriving Show

data GhcSpecSig = SpSig
  { gsTySigs   :: ![(Var, LocSpecType)]           -- ^ Asserted Reftypes
  , gsAsmSigs  :: ![(Var, LocSpecType)]           -- ^ Assumed Reftypes
  , gsAsmReflects  :: ![(Var, Var)]               -- ^ Assumed Reftypes (left is the actual function name and right the pretended one)
  , gsRefSigs  :: ![(Var, LocSpecType)]           -- ^ Reflected Reftypes
  , gsInSigs   :: ![(Var, LocSpecType)]           -- ^ Auto generated Signatures
  , gsNewTypes :: ![(TyCon, LocSpecType)]         -- ^ Mapping of 'newtype' type constructors with their refined types.
  , gsDicts    :: !(DEnv Var LocSpecType)            -- ^ Refined Classes from Instances
  , gsMethods  :: ![(Var, MethodType LocSpecType)]   -- ^ Refined Classes from Classes
  , gsTexprs   :: ![(Var, LocSpecType, [F.Located F.Expr])]  -- ^ Lexicographically ordered expressions for termination
  , gsRelation :: ![(Var, Var, LocSpecType, LocSpecType, RelExpr, RelExpr)]
  , gsAsmRel   :: ![(Var, Var, LocSpecType, LocSpecType, RelExpr, RelExpr)]
  }
  deriving Show

instance Semigroup GhcSpecSig where
  x <> y = SpSig
    { gsTySigs   = gsTySigs x   <> gsTySigs y
    , gsAsmSigs  = gsAsmSigs x  <> gsAsmSigs y
    , gsAsmReflects = gsAsmReflects x <> gsAsmReflects y
    , gsRefSigs  = gsRefSigs x  <> gsRefSigs y
    , gsInSigs   = gsInSigs x   <> gsInSigs y
    , gsNewTypes = gsNewTypes x <> gsNewTypes y
    , gsDicts    = gsDicts x    <> gsDicts y
    , gsMethods  = gsMethods x  <> gsMethods y
    , gsTexprs   = gsTexprs x   <> gsTexprs y
    , gsRelation = gsRelation x <> gsRelation y
    , gsAsmRel   = gsAsmRel x   <> gsAsmRel y
    }







instance Monoid GhcSpecSig where
  mempty = SpSig mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty

data GhcSpecData = SpData
  { gsCtors      :: ![(Var, LocSpecType)]         -- ^ Data Constructor Measure Sigs
  , gsMeas       :: ![(F.Symbol, LocSpecType)]    -- ^ Measure Types eg.  len :: [a] -> Int
  , gsInvariants :: ![(Maybe Var, LocSpecType)]   -- ^ Data type invariants from measure definitions, e.g forall a. {v: [a] | len(v) >= 0}
  , gsIaliases   :: ![(LocSpecType, LocSpecType)] -- ^ Data type invariant aliases
  , gsMeasures   :: ![Measure SpecType DataCon]   -- ^ Measure definitions
  , gsOpaqueRefls:: ![Var]                        -- ^ List of opaque reflected measures
  , gsUnsorted   :: ![UnSortedExpr]
  }
  deriving Show

data GhcSpecNames = SpNames
  { gsFreeSyms   :: ![(F.Symbol, Var)]            -- ^ List of `Symbol` free in spec and corresponding GHC var, eg. (Cons, Cons#7uz) from tests/pos/ex1.hs
  , gsDconsP     :: ![F.Located DataCon]          -- ^ Predicated Data-Constructors, e.g. see tests/pos/Map.hs
  , gsTconsP     :: ![TyConP]                     -- ^ Predicated Type-Constructors, e.g. see tests/pos/Map.hs
  , gsTcEmbeds   :: !(F.TCEmb TyCon)              -- ^ Embedding GHC Tycons into fixpoint sorts e.g. "embed Set as Set_set"
  , gsADTs       :: ![F.DataDecl]                 -- ^ ADTs extracted from Haskell 'data' definitions
  , gsTyconEnv   :: !TyConMap
  }
  deriving Show

deriving instance Show TyConMap

data GhcSpecTerm = SpTerm
  { gsStTerm     :: !(S.HashSet Var)              -- ^ Binders to CHECK by structural termination
  , gsAutosize   :: !(S.HashSet TyCon)            -- ^ Binders to IGNORE during termination checking
  , gsLazy       :: !(S.HashSet Var)              -- ^ Binders to IGNORE during termination checking
  , gsFail       :: !(S.HashSet (F.Located Var))    -- ^ Binders to fail type checking
  , gsNonStTerm  :: !(S.HashSet Var)              -- ^ Binders to CHECK using REFINEMENT-TYPES/termination metrics
  }
  deriving Show

instance Semigroup GhcSpecTerm where
  t1 <> t2 = SpTerm
    { gsStTerm    = gsStTerm t1    <> gsStTerm t2
    , gsAutosize  = gsAutosize t1  <> gsAutosize t2
    , gsLazy      = gsLazy t1      <> gsLazy t2
    , gsFail      = gsFail t1      <> gsFail t2
    , gsNonStTerm = gsNonStTerm t1 <> gsNonStTerm t2
    }

instance Monoid GhcSpecTerm where
  mempty = SpTerm mempty mempty mempty mempty mempty
data GhcSpecRefl = SpRefl
  { gsAutoInst     :: !(S.HashSet Var)                  -- ^ Binders to USE PLE
  , gsHAxioms      :: ![(Var, LocSpecType, F.Equation)] -- ^ Lifted definitions
  , gsImpAxioms    :: ![F.Equation]                     -- ^ Axioms from imported reflected functions
  , gsMyAxioms     :: ![F.Equation]                     -- ^ Axioms from my reflected functions
  , gsReflects     :: ![Var]                            -- ^ Binders for reflected functions
  , gsLogicMap     :: !LogicMap
  , gsRewrites     :: S.HashSet (F.Located Var)
  , gsRewritesWith :: M.HashMap Var [Var]
  }
  deriving Show

instance Semigroup GhcSpecRefl where
  x <> y = SpRefl
    { gsAutoInst = gsAutoInst x <> gsAutoInst y
    , gsHAxioms  = gsHAxioms x <> gsHAxioms y
    , gsImpAxioms = gsImpAxioms x <> gsImpAxioms y
    , gsMyAxioms = gsMyAxioms x <> gsMyAxioms y
    , gsReflects = gsReflects x <> gsReflects y
    , gsLogicMap = gsLogicMap x <> gsLogicMap y
    , gsRewrites = gsRewrites x <> gsRewrites y
    , gsRewritesWith = gsRewritesWith x <> gsRewritesWith y
    }

instance Monoid GhcSpecRefl where
  mempty = SpRefl mempty mempty mempty
                  mempty mempty mempty
                  mempty mempty

type VarOrLocSymbol = Either Var LocSymbol
type BareMeasure   = Measure LocBareType (F.Located LHName)
type BareDef       = Def     LocBareType (F.Located LHName)
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
type BareSpec = Spec F.Symbol BareType
type BareSpecLHName = Spec LHName BareTypeLHName
type BareSpecParsed = Spec LocSymbol BareTypeParsed

-- | A generic 'Spec' type, polymorphic over the inner choice of type and binders.
--
-- @lname@ corresponds to the names used for entities only known to LH like
-- non-interpreted functions and type aliases.
data Spec lname ty = Spec
  { measures   :: ![MeasureV lname (F.Located ty) (F.Located LHName)] -- ^ User-defined properties for ADTs
  , expSigs    :: ![(lname, F.Sort)]                                  -- ^ Exported logic symbols originated by reflecting functions
  , asmSigs    :: ![(F.Located LHName, F.Located ty)]                 -- ^ Assumed (unchecked) types; including reflected signatures
  , asmReflectSigs :: ![(F.Located LHName, F.Located LHName)]         -- ^ Assume reflects : left is the actual function and right the pretended one
  , sigs       :: ![(F.Located LHName, F.Located (BareTypeV lname))]  -- ^ Asserted spec signatures
  , invariants :: ![(Maybe F.LocSymbol, F.Located ty)]                -- ^ Data type invariants; the Maybe is the generating measure
  , ialiases   :: ![(F.Located ty, F.Located ty)]                     -- ^ Data type invariants to be checked
  , dataDecls  :: ![DataDeclP lname ty]                               -- ^ Predicated data definitions
  , newtyDecls :: ![DataDeclP lname ty]                               -- ^ Predicated new type definitions
  , aliases    :: ![F.Located (RTAlias F.Symbol (BareTypeV lname))]   -- ^ RefType aliases
  , ealiases   :: ![F.Located (RTAlias F.Symbol (F.ExprV lname))]     -- ^ Expression aliases
  , embeds     :: !(F.TCEmb (F.Located LHName))                       -- ^ GHC-Tycon-to-fixpoint Tycon map
  , qualifiers :: ![F.QualifierV lname]                               -- ^ Qualifiers in source files
  , lvars      :: !(S.HashSet (F.Located LHName))                     -- ^ Variables that should be checked in the environment they are used
  , lazy       :: !(S.HashSet (F.Located LHName))                     -- ^ Ignore Termination Check in these Functions
  , rewrites    :: !(S.HashSet (F.Located LHName))                    -- ^ Theorems turned into rewrite rules
  , rewriteWith :: !(M.HashMap (F.Located LHName) [F.Located LHName]) -- ^ Definitions using rewrite rules
  , fails      :: !(S.HashSet (F.Located LHName))                     -- ^ These Functions should be unsafe
  , reflects   :: !(S.HashSet (F.Located LHName))                     -- ^ Binders to reflect
  , privateReflects :: !(S.HashSet F.LocSymbol)                       -- ^ Private binders to reflect
  , opaqueReflects :: !(S.HashSet (F.Located LHName))                 -- ^ Binders to opaque-reflect
  , autois     :: !(S.HashSet (F.Located LHName))                     -- ^ Automatically instantiate axioms in these Functions
  , hmeas      :: !(S.HashSet (F.Located LHName))                     -- ^ Binders to turn into measures using haskell definitions
  , inlines    :: !(S.HashSet (F.Located LHName))                     -- ^ Binders to turn into logic inline using haskell definitions
  , ignores    :: !(S.HashSet (F.Located LHName))                     -- ^ Binders to ignore during checking; that is DON't check the corebind.
  , autosize   :: !(S.HashSet (F.Located LHName))                     -- ^ Type Constructors that get automatically sizing info
  , pragmas    :: ![F.Located String]                                 -- ^ Command-line configurations passed in through source
  , cmeasures  :: ![MeasureV lname (F.Located ty) ()]                 -- ^ Measures attached to a type-class
  , imeasures  :: ![MeasureV lname (F.Located ty) (F.Located LHName)] -- ^ Mappings from (measure,type) -> measure
  , omeasures  :: ![MeasureV lname (F.Located ty) (F.Located LHName)] -- ^ Opaque reflection measures.
  -- Separate field bc measures are checked for duplicates, and we want to allow for opaque-reflected measures to be duplicated.
  -- See Note [Duplicate measures and opaque reflection] in "Language.Haskell.Liquid.Measure".
  , classes    :: ![RClass (F.Located ty)]                            -- ^ Refined Type-Classes
  , relational :: ![(F.Located LHName, F.Located LHName, F.Located (BareTypeV lname), F.Located (BareTypeV lname), RelExprV lname, RelExprV lname)] -- ^ Relational types
  , asmRel :: ![(F.Located LHName, F.Located LHName, F.Located (BareTypeV lname), F.Located (BareTypeV lname), RelExprV lname, RelExprV lname)] -- ^ Assumed relational types
  , termexprs  :: ![(F.Located LHName, [F.Located (F.ExprV lname)])]  -- ^ Terminating Conditions for functions
  , rinstance  :: ![RInstance (F.Located ty)]
  , dvariance  :: ![(F.Located LHName, [Variance])]                   -- ^ TODO ? Where do these come from ?!
  , dsize      :: ![([F.Located ty], lname)]                          -- ^ Size measure to enforce fancy termination
  , bounds     :: !(RRBEnvV lname (F.Located ty))
  , axeqs      :: ![F.EquationV lname]                                -- ^ Equalities used for Proof-By-Evaluation
  } deriving (Data, Generic)

instance (Show lname, F.PPrint lname, Show ty, F.PPrint ty, F.PPrint (RTypeV lname BTyCon BTyVar (RReftV lname))) => F.PPrint (Spec lname ty) where
    pprintTidy k sp = text "dataDecls = " <+> pprintTidy k  (dataDecls sp)
                         HughesPJ.$$
                      text "classes = " <+> pprintTidy k (classes sp)
                         HughesPJ.$$
                      text "sigs = " <+> pprintTidy k (sigs sp)

deriving instance Show BareSpec

-- | A function to resolve names in the ty parameter of Spec
--
--
emapSpecM
  :: Monad m
  =>
     -- | The bscope setting, which affects which names
     -- are considered to be in scope in refinment types.
     Bool
     -- | For names that have a local environment return the names in scope.
  -> (LHName -> [F.Symbol])
     -- | The first parameter of the function argument are the variables in scope.
  -> ([F.Symbol] -> lname0 -> m lname1)
  -> ([F.Symbol] -> ty0 -> m ty1)
  -> Spec lname0 ty0
  -> m (Spec lname1 ty1)
emapSpecM bscp lenv vf f sp = do
    measures <- mapM (emapMeasureM vf (traverse . f)) (measures sp)
    expSigs <- sequence [ (,s) <$> vf [] n | (n, s) <- expSigs sp ]
    asmSigs <- mapM (\p -> traverse (traverse (f $ lenv $ val $ fst p)) p) (asmSigs sp)
    sigs <-
      mapM
        (\p -> traverse (traverse (emapBareTypeVM bscp vf (lenv $ val $ fst p))) p)
        (sigs sp)
    invariants <- mapM (traverse (traverse fnull)) (invariants sp)
    ialiases <- mapM (bimapM (traverse fnull) (traverse fnull)) (ialiases sp)
    dataDecls <- mapM (emapDataDeclM bscp vf f) (dataDecls sp)
    newtyDecls <- mapM (emapDataDeclM bscp vf f) (newtyDecls sp)
    aliases <- mapM (traverse (emapRTAlias (emapBareTypeVM bscp vf))) (aliases sp)
    ealiases <- mapM (traverse (emapRTAlias (\e -> emapExprVM (vf . (++ e))))) $ ealiases sp
    qualifiers <- mapM (emapQualifierM vf) $ qualifiers sp
    cmeasures <- mapM (emapMeasureM vf (traverse . f)) (cmeasures sp)
    imeasures <- mapM (emapMeasureM vf (traverse . f)) (imeasures sp)
    omeasures <- mapM (emapMeasureM vf (traverse . f)) (omeasures sp)
    classes <- mapM (traverse (traverse fnull)) (classes sp)
    relational <- mapM (emapRelationalM vf) (relational sp)
    asmRel <- mapM (emapRelationalM vf) (asmRel sp)
    let mbinds = Lazy.M.fromList [ (val lx, ty_binds $ toRTypeRep $ val lty) | (lx, lty) <- sigs ]
    termexprs <-
      mapM
        (\p -> do
          let bs0 = lenv $ val $ fst p
              mbs = M.findWithDefault [] (val $ fst p) mbinds
          traverse
            (mapM (traverse (emapExprVM (vf . (++ (mbs ++ bs0))))))
            p
        )
        (termexprs sp)
    rinstance <- mapM (traverse (traverse fnull)) (rinstance sp)
    dsize <- mapM (bimapM (mapM (traverse fnull)) (vf [])) (dsize sp)
    bounds <- M.fromList <$>
      mapM
        (traverse (emapBoundM (traverse . f) (\e -> emapExprVM (vf . (++ e)))))
        (M.toList $ bounds sp)
    axeqs <- mapM (emapEquationM vf) $ axeqs sp
    return sp
      { measures
      , expSigs
      , asmSigs
      , sigs
      , invariants
      , ialiases
      , dataDecls
      , newtyDecls
      , aliases
      , ealiases
      , qualifiers
      , cmeasures
      , imeasures
      , omeasures
      , classes
      , relational
      , asmRel
      , termexprs
      , rinstance
      , dsize
      , bounds
      , axeqs
      }
  where
    fnull = f []
    emapRelationalM vf1 (n0, n1, t0, t1, e0, e1) = do
      t0' <- traverse (emapBareTypeVM bscp vf1 []) t0
      t1' <- traverse (emapBareTypeVM bscp vf1 []) t1
      let bs = [F.symbol "r1", F.symbol "r2"] ++ tArgs (val t0') ++ tArgs (val t1')
      e0' <- emapRelExprV (vf1 . (++ bs)) e0
      e1' <- emapRelExprV (vf1 . (++ bs)) e1
      return (n0, n1, t0', t1', e0', e1')

    tArgs t =
      let rt = toRTypeRep t
       in ty_binds rt ++ concatMap tArgs (ty_args rt)

emapRTAlias :: Monad m => ([F.Symbol] -> r0 -> m r1) -> RTAlias F.Symbol r0 -> m (RTAlias F.Symbol r1)
emapRTAlias f rt = do
    rtBody <- f (rtTArgs rt ++ rtVArgs rt) (rtBody rt)
    return rt{rtBody}

emapQualifierM :: Monad m => ([F.Symbol] -> v0 -> m v1) -> F.QualifierV v0 -> m (F.QualifierV v1)
emapQualifierM f q = do
    qBody <- emapExprVM (f . (++ map F.qpSym (F.qParams q))) (F.qBody q)
    return q{F.qBody}

emapEquationM :: Monad m => ([F.Symbol] -> v0 -> m v1) -> F.EquationV v0 -> m (F.EquationV v1)
emapEquationM f e = do
    eqBody <- emapExprVM (f . (++ map fst (F.eqArgs e))) (F.eqBody e)
    return e{F.eqBody}

mapSpecTy :: (ty0 -> ty1) -> Spec lname ty0 -> Spec lname ty1
mapSpecTy f Spec {..} =
    Spec
      { measures = map (mapMeasureTy (fmap f)) measures
      , asmSigs = map (fmap (fmap f)) asmSigs
      , invariants = map (fmap (fmap f)) invariants
      , ialiases = map (bimap (fmap f) (fmap f)) ialiases
      , dataDecls = map (fmap f) dataDecls
      , newtyDecls = map (fmap f) newtyDecls
      , cmeasures = map (mapMeasureTy (fmap f)) cmeasures
      , imeasures = map (mapMeasureTy (fmap f)) imeasures
      , omeasures = map (mapMeasureTy (fmap f)) omeasures
      , classes = map (fmap (fmap f)) classes
      , rinstance = map (fmap (fmap f)) rinstance
      , dsize = map (first (map (fmap f))) dsize
      , bounds = M.map (first (fmap f)) bounds
      , ..
      }

mapSpecLName :: (lname0 -> lname1) -> Spec lname0 ty -> Spec lname1 ty
mapSpecLName f Spec {..} =
    Spec
      { measures = map (mapMeasureV f) measures
      , expSigs = map (first f) expSigs
      , sigs = map (fmap (fmap (mapRTypeV f . mapReft (mapUReftV f (fmap f))))) sigs
      , dataDecls = map (mapDataDeclV f) dataDecls
      , newtyDecls = map (mapDataDeclV f) newtyDecls
      , aliases = map (fmap (fmap (mapRTypeV f . fmap (mapUReftV f (fmap f))))) aliases
      , ealiases = map (fmap (fmap (fmap f))) ealiases
      , qualifiers = map (fmap f) qualifiers
      , cmeasures = map (mapMeasureV f) cmeasures
      , imeasures = map (mapMeasureV f) imeasures
      , omeasures = map (mapMeasureV f) omeasures
      , relational = map (mapRelationalV f) relational
      , asmRel = map (mapRelationalV f) asmRel
      , termexprs = map (fmap (map (fmap (fmap f)))) termexprs
      , bounds = M.map (fmap (fmap f)) bounds
      , axeqs = map (fmap f) axeqs
      , dsize = map (fmap f) dsize
      , ..
      }
  where
    mapRelationalV f1 (n0, n1, a, b, e0, e1) =
      (n0, n1, fmap (mapRTypeV f1 . mapReft (mapUReftV f1 (fmap f1))) a, fmap (mapRTypeV f1 . mapReft (mapUReftV f1 (fmap f1))) b, fmap f1 e0, fmap f1 e1)

-- /NOTA BENE/: These instances below are considered legacy, because merging two 'Spec's together doesn't
-- really make sense, and we provide this only for legacy purposes.
instance Semigroup (Spec lname ty) where
  s1 <> s2
    = Spec { measures   =           measures   s1 ++ measures   s2
           , expSigs    =           expSigs    s1 ++ expSigs    s2
           , asmSigs    =           asmSigs    s1 ++ asmSigs    s2
           , asmReflectSigs    =    asmReflectSigs s1 ++ asmReflectSigs s2
           , sigs       =           sigs       s1 ++ sigs       s2
           , invariants =           invariants s1 ++ invariants s2
           , ialiases   =           ialiases   s1 ++ ialiases   s2
           , dataDecls  =           dataDecls  s1 ++ dataDecls  s2
           , newtyDecls =           newtyDecls s1 ++ newtyDecls s2
           , aliases    =           aliases    s1 ++ aliases    s2
           , ealiases   =           ealiases   s1 ++ ealiases   s2
           , qualifiers =           qualifiers s1 ++ qualifiers s2
           , pragmas    =           pragmas    s1 ++ pragmas    s2
           , cmeasures  =           cmeasures  s1 ++ cmeasures  s2
           , imeasures  =           imeasures  s1 ++ imeasures  s2
           , omeasures  =           omeasures  s1 ++ omeasures  s2
           , classes    =           classes    s1 ++ classes    s2
           , relational =           relational s1 ++ relational s2
           , asmRel     =           asmRel     s1 ++ asmRel     s2
           , termexprs  =           termexprs  s1 ++ termexprs  s2
           , rinstance  =           rinstance  s1 ++ rinstance  s2
           , dvariance  =           dvariance  s1 ++ dvariance  s2
           , dsize      =               dsize  s1 ++ dsize      s2
           , axeqs      =           axeqs s1      ++ axeqs s2
           , embeds     = mappend   (embeds   s1)  (embeds   s2)
           , lvars      = S.union   (lvars    s1)  (lvars    s2)
           , lazy       = S.union   (lazy     s1)  (lazy     s2)
           , rewrites   = S.union   (rewrites    s1)  (rewrites    s2)
           , rewriteWith = M.union  (rewriteWith s1)  (rewriteWith s2)
           , fails      = S.union   (fails    s1)  (fails    s2)
           , reflects   = S.union   (reflects s1)  (reflects s2)
           , privateReflects = S.union (privateReflects s1) (privateReflects s2)
           , opaqueReflects   = S.union   (opaqueReflects s1)  (opaqueReflects s2)
           , hmeas      = S.union   (hmeas    s1)  (hmeas    s2)
           , inlines    = S.union   (inlines  s1)  (inlines  s2)
           , ignores    = S.union   (ignores  s1)  (ignores  s2)
           , autosize   = S.union   (autosize s1)  (autosize s2)
           , bounds     = M.union   (bounds   s1)  (bounds   s2)
           , autois     = S.union   (autois s1)      (autois s2)
           }

instance Monoid (Spec lname ty) where
  mappend = (<>)
  mempty
    = Spec { measures   = []
           , expSigs    = []
           , asmSigs    = []
           , asmReflectSigs = []
           , sigs       = []
           , invariants = []
           , ialiases   = []
           , dataDecls  = []
           , newtyDecls = []
           , aliases    = []
           , ealiases   = []
           , embeds     = mempty
           , qualifiers = []
           , lvars      = S.empty
           , lazy       = S.empty
           , rewrites   = S.empty
           , rewriteWith = M.empty
           , fails      = S.empty
           , autois     = S.empty
           , hmeas      = S.empty
           , reflects   = S.empty
           , privateReflects = S.empty
           , opaqueReflects = S.empty
           , inlines    = S.empty
           , ignores    = S.empty
           , autosize   = S.empty
           , pragmas    = []
           , cmeasures  = []
           , imeasures  = []
           , omeasures  = []
           , classes    = []
           , relational = []
           , asmRel     = []
           , termexprs  = []
           , rinstance  = []
           , dvariance  = []
           , dsize      = []
           , axeqs      = []
           , bounds     = M.empty
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
-- * The 'reflSigs', they are now just \"normal\" signatures;
-- * The 'lazy', we don't do termination checking in lifted specs;
-- * The 'reflects', the reflection has already happened at this point;
-- * The 'hmeas', we have /already/ turned these into measures at this point;
-- * The 'inlines', ditto as 'hmeas';
-- * The 'ignores', ditto as 'hmeas';
-- * The 'pragmas', we can't make any use of this information for lifted specs;
-- * The 'termexprs', we don't do termination checking in lifted specs;
--
-- Apart from less fields, a 'LiftedSpec' /replaces all instances of lists with sets/, to enforce
-- duplicate detection and removal on what we serialise on disk.
data LiftedSpec = LiftedSpec
  { -- | Measures (a.k.a.  user-defined properties for ADTs)
    --
    -- The key of the HashMap is the unqualified name of the measure.
    -- Constructing such a map discards preceding measures with the same name
    -- as later measures, which makes possible to predict which of a few
    -- conflicting measures will be exported.
    --
    -- Tested in MeasureOverlapC.hs
    liftedMeasures   :: HashMap F.Symbol (MeasureV LHName LocBareTypeLHName (F.Located LHName))
  , liftedExpSigs    :: HashSet (LHName, F.Sort)
    -- ^ Exported logic symbols originated from reflecting functions
  , liftedPrivateReflects :: HashSet F.LocSymbol
    -- ^ Private functions that have been reflected
  , liftedAsmSigs    :: HashSet (F.Located LHName, LocBareTypeLHName)
    -- ^ Assumed (unchecked) types; including reflected signatures
  , liftedSigs       :: HashSet (F.Located LHName, LocBareTypeLHName)
    -- ^ Asserted spec signatures
  , liftedInvariants :: HashSet (Maybe F.LocSymbol, LocBareTypeLHName)
    -- ^ Data type invariants; the Maybe is the generating measure
  , liftedIaliases   :: HashSet (LocBareTypeLHName, LocBareTypeLHName)
    -- ^ Data type invariants to be checked
  , liftedDataDecls  :: HashSet DataDeclLHName
    -- ^ Predicated data definitions
  , liftedNewtyDecls :: HashSet DataDeclLHName
    -- ^ Predicated new type definitions
  , liftedAliases    :: HashSet (F.Located (RTAlias F.Symbol BareTypeLHName))
    -- ^ RefType aliases
  , liftedEaliases   :: HashSet (F.Located (RTAlias F.Symbol (F.ExprV LHName)))
    -- ^ Expression aliases
  , liftedEmbeds     :: F.TCEmb (F.Located LHName)
    -- ^ GHC-Tycon-to-fixpoint Tycon map
  , liftedQualifiers :: HashSet (F.QualifierV LHName)
    -- ^ Qualifiers in source/spec files
  , liftedLvars      :: HashSet (F.Located LHName)
    -- ^ Variables that should be checked in the environment they are used
  , liftedAutois     :: S.HashSet (F.Located LHName)
    -- ^ Automatically instantiate axioms in these Functions
  , liftedAutosize   :: HashSet (F.Located LHName)
    -- ^ Type Constructors that get automatically sizing info

    -- | Measures attached to a type-class
    --
    -- Imitates the arrangement for 'liftedMeasures'
  , liftedCmeasures  :: HashMap F.Symbol (MeasureV LHName LocBareTypeLHName ())
  , liftedImeasures  :: HashSet (MeasureV LHName LocBareTypeLHName (F.Located LHName))
    -- ^ Mappings from (measure,type) -> measure
  , liftedOmeasures  :: HashSet (MeasureV LHName LocBareTypeLHName (F.Located LHName))
    -- ^ Lifted opaque reflection measures
  , liftedClasses    :: HashSet (RClass LocBareTypeLHName)
    -- ^ Refined Type-Classes
  , liftedRinstance  :: HashSet (RInstance LocBareTypeLHName)
  , liftedDsize      :: [([LocBareTypeLHName], LHName)]
  , liftedDvariance  :: HashSet (F.Located LHName, [Variance])
    -- ^ ? Where do these come from ?!
  , liftedBounds     :: RRBEnvV LHName LocBareTypeLHName
  , liftedAxeqs      :: HashSet (F.EquationV LHName)
    -- ^ Equalities used for Proof-By-Evaluation
  } deriving (Eq, Data, Generic)
    deriving Hashable via Generically LiftedSpec
    deriving Binary   via Generically LiftedSpec


instance Show LiftedSpec where
   show = (show :: BareSpec -> String) . fromBareSpecLHName . unsafeFromLiftedSpec

fromBareSpecLHName :: BareSpecLHName -> BareSpec
fromBareSpecLHName sp =
    mapSpecTy
      ( mapRTypeV lhNameToResolvedSymbol .
        mapReft (mapUReftV lhNameToResolvedSymbol (fmap lhNameToResolvedSymbol))
      ) $
    mapSpecLName lhNameToResolvedSymbol sp

fromBareSpecParsed :: BareSpecParsed -> BareSpec
fromBareSpecParsed sp =
    mapSpecTy
      ( mapRTypeV val .
        mapReft (mapUReftV val (fmap val))
      ) $
    mapSpecLName val sp

emptyLiftedSpec :: LiftedSpec
emptyLiftedSpec = LiftedSpec
  { liftedMeasures = mempty
  , liftedExpSigs  = mempty
  , liftedPrivateReflects = mempty
  , liftedAsmSigs  = mempty
  , liftedSigs     = mempty
  , liftedInvariants = mempty
  , liftedIaliases   = mempty
  , liftedDataDecls  = mempty
  , liftedNewtyDecls = mempty
  , liftedAliases    = mempty
  , liftedEaliases   = mempty
  , liftedEmbeds     = mempty
  , liftedQualifiers = mempty
  , liftedLvars      = mempty
  , liftedAutois     = mempty
  , liftedAutosize   = mempty
  , liftedCmeasures  = mempty
  , liftedImeasures  = mempty
  , liftedOmeasures  = mempty
  , liftedClasses    = mempty
  , liftedRinstance  = mempty
  , liftedDvariance  = mempty
  , liftedDsize      = mempty
  , liftedBounds     = mempty
  , liftedAxeqs      = mempty
  }

-- $trackingDeps

-- | The /target/ dependencies that concur to the creation of a 'TargetSpec' and a 'LiftedSpec'.
newtype TargetDependencies =
  TargetDependencies { getDependencies :: HashMap StableModule LiftedSpec }
  deriving (Data, Eq, Show, Generic)
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
isPLEVar sp x = S.member x (gsAutoInst (gsRefl sp))

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
  { _giTarget    :: !FilePath              -- ^ Source file for module
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
  , _gsImps   :: ![(F.Symbol, F.Sort)]  -- ^ Imported Environment
  , _gsConfig :: !Config
  , _gsLSpec  :: !(Spec F.Symbol BareType) -- ^ Lifted specification for the target module
  }

instance HasConfig GhcSpec where
  getConfig = _gsConfig


toTargetSrc :: GhcSrc -> TargetSrc
toTargetSrc a = TargetSrc
  { giTarget    = _giTarget a
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

fromTargetSrc :: TargetSrc -> GhcSrc
fromTargetSrc a = Src
  { _giTarget    = giTarget a
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

toTargetSpec ::  GhcSpec -> TargetSpec
toTargetSpec ghcSpec = TargetSpec
      { gsSig    = _gsSig ghcSpec
      , gsQual   = _gsQual ghcSpec
      , gsData   = _gsData ghcSpec
      , gsName   = _gsName ghcSpec
      , gsVars   = _gsVars ghcSpec
      , gsTerm   = _gsTerm ghcSpec
      , gsRefl   = _gsRefl ghcSpec
      , gsImps   = _gsImps ghcSpec
      , gsConfig = _gsConfig ghcSpec
      }

toLiftedSpec :: BareSpecLHName -> LiftedSpec
toLiftedSpec a = LiftedSpec
  { liftedMeasures   =
      M.fromList
        [ (dropModuleNames $ lhNameToResolvedSymbol n, m)
        | m <- measures a
        , let n = val $ msName m
        ]
  , liftedExpSigs    = S.fromList . expSigs  $ a
  , liftedPrivateReflects = privateReflects a
  , liftedAsmSigs    = S.fromList . asmSigs  $ a
  , liftedSigs       = S.fromList . sigs     $ a
  , liftedInvariants = S.fromList . invariants $ a
  , liftedIaliases   = S.fromList . ialiases $ a
  , liftedDataDecls  = S.fromList . dataDecls $ a
  , liftedNewtyDecls = S.fromList . newtyDecls $ a
  , liftedAliases    = S.fromList . aliases $ a
  , liftedEaliases   = S.fromList . ealiases $ a
  , liftedEmbeds     = embeds a
  , liftedQualifiers = S.fromList . qualifiers $ a
  , liftedLvars      = lvars a
  , liftedAutois     = autois a
  , liftedAutosize   = autosize a
  , liftedCmeasures  =
      M.fromList
        [ (dropModuleNames $ lhNameToResolvedSymbol n, m)
        | m <- cmeasures a
        , let n = val $ msName m
        ]
  , liftedImeasures  = S.fromList . imeasures $ a
  , liftedOmeasures  = S.fromList . omeasures $ a
  , liftedClasses    = S.fromList . classes $ a
  , liftedRinstance  = S.fromList . rinstance $ a
  , liftedDvariance  = S.fromList . dvariance $ a
  , liftedDsize      = dsize a
  , liftedBounds     = bounds a
  , liftedAxeqs      = S.fromList . axeqs $ a
  }

-- This is a temporary internal function that we use to convert the input dependencies into a format
-- suitable for 'makeGhcSpec'.
unsafeFromLiftedSpec :: LiftedSpec -> BareSpecLHName
unsafeFromLiftedSpec a = Spec
  { measures   = M.elems $ liftedMeasures a
  , expSigs    = S.toList . liftedExpSigs $ a
  , asmSigs    = S.toList . liftedAsmSigs $ a
  , asmReflectSigs = mempty
  , sigs       = S.toList . liftedSigs $ a
  , relational = mempty
  , asmRel     = mempty
  , invariants = S.toList . liftedInvariants $ a
  , ialiases   = S.toList . liftedIaliases $ a
  , dataDecls  = S.toList . liftedDataDecls $ a
  , newtyDecls = S.toList . liftedNewtyDecls $ a
  , aliases    = S.toList . liftedAliases $ a
  , ealiases   = S.toList . liftedEaliases $ a
  , embeds     = liftedEmbeds a
  , qualifiers = S.toList . liftedQualifiers $ a
  , lvars      = liftedLvars a
  , lazy       = mempty
  , fails      = mempty
  , rewrites   = mempty
  , rewriteWith = mempty
  , reflects   = mempty
  , privateReflects = liftedPrivateReflects a
  , opaqueReflects   = mempty
  , autois     = liftedAutois a
  , hmeas      = mempty
  , inlines    = mempty
  , ignores    = mempty
  , autosize   = liftedAutosize a
  , pragmas    = mempty
  , cmeasures  = M.elems $ liftedCmeasures a
  , imeasures  = S.toList . liftedImeasures $ a
  , omeasures  = S.toList . liftedOmeasures $ a
  , classes    = S.toList . liftedClasses $ a
  , termexprs  = mempty
  , rinstance  = S.toList . liftedRinstance $ a
  , dvariance  = S.toList . liftedDvariance $ a
  , dsize      = liftedDsize  a
  , bounds     = liftedBounds a
  , axeqs      = S.toList . liftedAxeqs $ a
  }
