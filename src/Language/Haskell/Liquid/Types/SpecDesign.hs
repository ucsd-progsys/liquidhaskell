{- | This module document a possible new design for spec types and type signatures -}

{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.Types.SpecDesign where

import           GHC.Generics                      hiding ( moduleName )
import qualified Control.Exception                       as Ex
import           Data.Binary                              ( Binary, get, put )
import qualified Language.Fixpoint.Types                 as F
import           Data.HashSet                             ( HashSet )
import qualified Data.HashMap.Strict                     as M
import           Data.HashMap.Strict                      ( HashMap )
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds
import           Language.Haskell.Liquid.GHC.API

-- Import qualified the old module, but let's get what we need only.
import qualified Language.Haskell.Liquid.Types.Specs as S

import           Outputable                               ( (<+>)
                                                          , text
                                                          , showSDocUnsafe
                                                          , ppr
                                                          )


{- | Transforming specs

Intuitively:

    +---------------+                                +-------------------+
    |   BareSpec    |                                |                   |  checked by liquid/liquidOne
    |               |                    ------------|    TargetSpec     |-----------------------------
    |(input module) |                   /            |                   |
    +---------------+  makeTargetSpec  /             +-------------------+
           +         -----------------/
    +---------------+                 \              +-------------------+
    | [LiftedSpec]  |                  \             |                   |    serialised on disk
    |               |                   -------------|    LiftedSpec     |-----------------------------
    |(dependencies) |                                |                   |
    +---------------+                                +-------------------+

-}

-- | The following is the overall type for /specifications/ obtained from
-- parsing the target source and dependent libraries
-- NOTE(adn) For now keeping the old names to minimise breakages.
data TargetInfo = TargetInfo
  { giSrc  :: !TargetSrc
  , giSpec :: !TargetSpec -- ^ All specification information for module
  }

-- | The 'TargetSrc' type is a collection of all the things we know about a module being currently
-- checked. It include things like the name of the module, the list of 'CoreBind's,
-- the 'TyCon's declared in this module (that includes 'TyCon's for classes), typeclass instances
-- and so and so forth. It might be thought as a sort of 'ModGuts' embellished with LH-specific
-- information (for example, 'giDefVars' are populated with datacons from the module plus the
-- let vars derived from the A-normalisation).
-- NOTE(adn) For now keeping the old names to minimise breakages.
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
  , gsExports   :: !NameSet               -- ^ `Name`s exported by the module being verified
  , gsFiTcs     :: ![TyCon]               -- ^ Family instance TyCons 
  , gsFiDcs     :: ![(F.Symbol, DataCon)] -- ^ Family instance DataCons 
  , gsPrimTcs   :: ![TyCon]               -- ^ Primitive GHC TyCons (from TysPrim.primTyCons)
  , gsQualImps  :: !QImports              -- ^ Map of qualified imports
  , gsAllImps   :: !(HashSet F.Symbol)    -- ^ Set of _all_ imported modules
  , gsTyThings  :: ![TyThing]             -- ^ All the @TyThing@s known to GHC
  }

-- | @QImports@ is a map of qualified imports. Used in 'GhcSrc' to hold the (qualified) imports for an
-- input module.
data QImports = QImports 
  { qiModules :: !(HashSet F.Symbol)            -- ^ All the modules that are imported qualified
  , qiNames   :: !(M.HashMap F.Symbol [F.Symbol]) -- ^ Map from qualification to full module name
  } deriving Show

-- | A 'TargetSpec' is what we /actually check via LiquidHaskell/. It is created as part of
-- 'mkTargetSpec' alongside the lifted spec.
data TargetSpec = TargetSpec
  { gsSig    :: !S.GhcSpecSig
  , gsQual   :: !S.GhcSpecQual
  , gsData   :: !S.GhcSpecData
  , gsName   :: !S.GhcSpecNames
  , gsVars   :: !S.GhcSpecVars
  , gsTerm   :: !S.GhcSpecTerm
  , gsRefl   :: !S.GhcSpecRefl
  , gsLaws   :: !S.GhcSpecLaws
  , gsImps   :: ![(F.Symbol, F.Sort)]  -- ^ Imported Environment
  , gsConfig :: !Config
  }


-- | A 'BareSpec' is the spec we derive by parsing the liquidhaskell annotations of a single file. As
-- such, it contains things which are relevant for validation and lifting; it contains things like
-- the pragmas the user defined, the termination condition (if termination-checking is enabled) and so
-- on and so forth. /Crucially/, as a 'BareSpec' is still subject to \"preflight checks\", it may contain
-- duplicates (e.g. duplicate measures, duplicate type declarations etc) and therefore most of the fields
-- for a 'BareSpec' are lists, so that we can report these errors to the end user: it would be an error
-- to silenty ignore the duplication and leave the duplicate resolution to whichever 'Eq' instance is
-- implemented for the relevant field.
newtype BareSpec    =
  MkBareSpec { getBareSpec :: S.Spec LocBareType F.LocSymbol }
  deriving (Generic, Show)

-- | A 'LiftedSpec' is derived from an input 'BareSpec' and a set of its dependencies.
-- The general motivations for lifting a spec are (a) name resolution, (b) the fact that some info is
-- only relevant for checking the body of functions but does not need to be exported, e.g. 
-- termination measures, or the fact that a type signature was assumed.
-- A 'LiftedSpec' is /what we serialise on disk and what the clients should will be using/.
--
-- What we /do not/ have compared to a 'BareSpec':
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
  { liftedMeasures   :: !(HashSet (Measure LocBareType F.LocSymbol))
    -- ^ User-defined properties for ADTs
  , liftedImpSigs    :: !(HashSet (F.Symbol, F.Sort))
    -- ^ Imported variables types
  , liftedExpSigs    :: !(HashSet (F.Symbol, F.Sort))
    -- ^ Exported variables types
  , liftedAsmSigs    :: !(HashSet (F.LocSymbol, LocBareType))
    -- ^ Assumed (unchecked) types; including reflected signatures
  , liftedSigs       :: !(HashSet (F.LocSymbol, LocBareType))
    -- ^ Imported functions and types
  , liftedInvariants :: !(HashSet (Maybe F.LocSymbol, LocBareType))
    -- ^ Data type invariants; the Maybe is the generating measure
  , liftedIaliases   :: !(HashSet (LocBareType, LocBareType))
    -- ^ Data type invariants to be checked
  , liftedImports    :: !(HashSet F.Symbol)
    -- ^ Loaded spec module names
  , liftedDataDecls  :: !(HashSet DataDecl)
    -- ^ Predicated data definitions
  , liftedNewtyDecls :: !(HashSet DataDecl)
    -- ^ Predicated new type definitions
  , liftedAliases    :: !(HashSet (F.Located (RTAlias F.Symbol BareType)))
    -- ^ RefType aliases
  , liftedEaliases   :: !(HashSet (F.Located (RTAlias F.Symbol F.Expr)))
    -- ^ Expression aliases
  , liftedEmbeds     :: !(F.TCEmb F.LocSymbol)
    -- ^ GHC-Tycon-to-fixpoint Tycon map
  , liftedQualifiers :: !(HashSet F.Qualifier)
    -- ^ Qualifiers in source/spec files
  , liftedDecr       :: !(HashSet (F.LocSymbol, [Int]))
    -- ^ Information on decreasing arguments
  , liftedLvars      :: !(HashSet F.LocSymbol)
    -- ^ Variables that should be checked in the environment they are used
  , liftedAutois     :: !(M.HashMap F.LocSymbol (Maybe Int))
    -- ^ Automatically instantiate axioms in these Functions with maybe specified fuel
  , liftedAutosize   :: !(HashSet F.LocSymbol)
    -- ^ Type Constructors that get automatically sizing info
  , liftedCmeasures  :: !(HashSet (Measure LocBareType ()))
    -- ^ Measures attached to a type-class
  , liftedImeasures  :: !(HashSet (Measure LocBareType F.LocSymbol))
    -- ^ Mappings from (measure,type) -> measure
  , liftedClasses    :: !(HashSet (RClass LocBareType))
    -- ^ Refined Type-Classes
  , liftedClaws      :: !(HashSet (RClass LocBareType))
    -- ^ Refined Type-Classe Laws
  , liftedRinstance  :: !(HashSet (RInstance LocBareType))
  , liftedIlaws      :: !(HashSet (RILaws LocBareType))
  , liftedDvariance  :: !(HashSet (F.LocSymbol, [Variance]))
    -- ^ ? Where do these come from ?!
  , liftedBounds     :: !(RRBEnv LocBareType)
  , liftedDefs       :: !(M.HashMap F.LocSymbol F.Symbol)
    -- ^ Temporary (?) hack to deal with dictionaries in specifications
    --   see tests/pos/NatClass.hs
  , liftedAxeqs      :: !(HashSet F.Equation)
    -- ^ Equalities used for Proof-By-Evaluation
  } deriving (Generic, Show)


-- | A newtype wrapper around a 'Module' which:
--
-- * Allows a 'Module' to be serialised (i.e. it has a 'Binary' instance)
-- * It tries to use stable comparison and equality under the hood.
--
newtype StableModule = StableModule Module

instance Ord StableModule where
  (StableModule m1) `compare` (StableModule m2) = stableModuleCmp m1 m2

instance Eq StableModule where
  (StableModule m1) == (StableModule m2) = (m1 `stableModuleCmp` m2) == EQ

instance Show StableModule where
    show (StableModule mdl) = "Stable" ++ debugShowModule mdl

-- | Converts a 'Module' into a 'StableModule'.
toStableModule :: Module -> StableModule
toStableModule = StableModule

instance Binary StableModule where

    put (StableModule mdl) = do
      put (unitIdString . moduleUnitId $ mdl)
      put (moduleNameString . moduleName $ mdl)

    get = do
      uidStr <- get
      mnStr  <- get
      pure $ StableModule (Module (stringToUnitId uidStr) (mkModuleName mnStr))

-- | FIXME(adn) This uses a 'ModName' for now for compatibility reasons, but theoretically we should
-- be using a 'StableModule'.
newtype TargetDependencies =
  TargetDependencies { getDependencies :: HashMap ModName LiftedSpec }

{------------------------------------------------------------------------------------------------------------
 Stubbed interface for creating and manipulating specs
------------------------------------------------------------------------------------------------------------}

-- | @makeTargetSpec@ constructs the @TargetSpec@ and then validates it using @validateTargetSpec@.
-- Upon success, the 'TargetSpec' and the 'LiftedSpec' are returned.
makeTargetSpec :: Config
               -> LogicMap
               -> TargetSrc
               -> BareSpec
               -> TargetDependencies
               -> (TargetSpec, LiftedSpec)
makeTargetSpec cfg lmap targetSrc dependencies = undefined

validateOrThrow :: Ex.Exception e => Either e c -> c
validateOrThrow = either Ex.throw id 

{------------------------------------------------------------------------------------------------------------
 Utility functions
------------------------------------------------------------------------------------------------------------}

debugShowModule :: Module -> String
debugShowModule m = showSDocUnsafe $
                     text "Module { unitId = " <+> ppr (moduleUnitId m)
                 <+> text ", name = " <+> ppr (moduleName m) 
                 <+> text " }"
