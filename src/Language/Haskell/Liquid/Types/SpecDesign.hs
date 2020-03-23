{- | This module document a possible new design for spec types and type signatures -}

{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}

module Language.Haskell.Liquid.Types.SpecDesign where

import           GHC.Generics                      hiding ( moduleName, to )
import           Data.Binary                              ( Binary, get, put )
import qualified Language.Fixpoint.Types                 as F
import           Data.Hashable
import           Data.HashSet                             ( HashSet )
import qualified Data.HashSet                            as HS
import qualified Data.HashMap.Strict                     as M
import           Data.HashMap.Strict                      ( HashMap )
import           Language.Haskell.Liquid.Types.Generics
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds
import           Language.Haskell.Liquid.GHC.API

-- Import qualified the old module, but let's get what we need only.
import qualified Language.Haskell.Liquid.Types.Specs     as S
import qualified Language.Haskell.Liquid.Bare            as Bare
import qualified Language.Haskell.Liquid.Bare.Check      as Bare

import           Optics
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

{------------------------------------------------------------------------------------------------------------
  Main spec types, which are mostly taken from the original 'Specs' module but they have been \"rebranded\"
  to better clarify their purposes. 
  Furthermore, we provide provisional compatibility ISOs and Prisms to smooth out the integration.
------------------------------------------------------------------------------------------------------------}

-- | The following is the overall type for /specifications/ obtained from
-- parsing the target source and dependent libraries. 
-- /IMPORTANT/: A 'TargetInfo' is what is /checked/ by LH itself and it /NEVER/ contains the 'LiftedSpec', 
-- because the checking happens only on the 'BareSpec' of the target module.
--
-- NOTE(adn) For now keeping the old names to minimise breakages.
data TargetInfo = TargetInfo
  { giSrc  :: !TargetSrc
  , giSpec :: !TargetSpec -- ^ All specification information for module
  }

instance HasConfig TargetInfo where
  getConfig = getConfig . giSpec

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
  , gsQualImps  :: !S.QImports            -- ^ Map of qualified imports
  , gsAllImps   :: !(HashSet F.Symbol)    -- ^ Set of _all_ imported modules
  , gsTyThings  :: ![TyThing]             -- ^ All the @TyThing@s known to GHC
  }

targetSrcIso :: Iso' S.GhcSrc TargetSrc
targetSrcIso = iso toTargetSrc fromTargetSrc
  where
    toTargetSrc a = TargetSrc
      { giIncDir    = S.giIncDir a
      , giTarget    = S.giTarget a
      , giTargetMod = S.giTargetMod a
      , giCbs       = S.giCbs a
      , gsTcs       = S.gsTcs a
      , gsCls       = S.gsCls a
      , giDerVars   = S.giDerVars a
      , giImpVars   = S.giImpVars a
      , giDefVars   = S.giDefVars a
      , giUseVars   = S.giUseVars a
      , gsExports   = S.gsExports a
      , gsFiTcs     = S.gsFiTcs a
      , gsFiDcs     = S.gsFiDcs a
      , gsPrimTcs   = S.gsPrimTcs a
      , gsQualImps  = S.gsQualImps a
      , gsAllImps   = S.gsAllImps a
      , gsTyThings  = S.gsTyThings a
      }

    fromTargetSrc a = S.Src
      { S.giIncDir    = giIncDir a
      , S.giTarget    = giTarget a
      , S.giTargetMod = giTargetMod a
      , S.giCbs       = giCbs a
      , S.gsTcs       = gsTcs a
      , S.gsCls       = gsCls a
      , S.giDerVars   = giDerVars a
      , S.giImpVars   = giImpVars a
      , S.giDefVars   = giDefVars a
      , S.giUseVars   = giUseVars a
      , S.gsExports   = gsExports a
      , S.gsFiTcs     = gsFiTcs a
      , S.gsFiDcs     = gsFiDcs a
      , S.gsPrimTcs   = gsPrimTcs a
      , S.gsQualImps  = gsQualImps a
      , S.gsAllImps   = gsAllImps a
      , S.gsTyThings  = gsTyThings a
      }

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

instance HasConfig TargetSpec where
  getConfig = gsConfig

targetSpecGetter :: Getter S.GhcSpec (TargetSpec, LiftedSpec)
targetSpecGetter = 
  to (\ghcSpec -> (toTargetSpec ghcSpec, view (to S.gsLSpec % liftedSpecGetter) ghcSpec))
  where
    toTargetSpec a = TargetSpec
      { gsSig    = S.gsSig a
      , gsQual   = S.gsQual a
      , gsData   = S.gsData a
      , gsName   = S.gsName a
      , gsVars   = S.gsVars a
      , gsTerm   = S.gsTerm a
      , gsRefl   = S.gsRefl a
      , gsLaws   = S.gsLaws a
      , gsImps   = S.gsImps a
      , gsConfig = S.gsConfig a
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
  deriving (Generic, Show, Semigroup, Monoid, Binary)

bareSpecIso :: Iso' S.BareSpec BareSpec
bareSpecIso = iso MkBareSpec getBareSpec

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
  } deriving (Eq, Generic, Show)
    deriving Hashable via Generically LiftedSpec 
    deriving Binary   via Generically LiftedSpec 


liftedSpecGetter :: Getter S.BareSpec LiftedSpec
liftedSpecGetter = to toLiftedSpec
  where
    toLiftedSpec a = LiftedSpec 
      { liftedMeasures   = HS.fromList . S.measures $ a
      , liftedImpSigs    = HS.fromList . S.impSigs  $ a
      , liftedExpSigs    = HS.fromList . S.expSigs  $ a
      , liftedAsmSigs    = HS.fromList . S.asmSigs  $ a
      , liftedSigs       = HS.fromList . S.sigs     $ a
      , liftedInvariants = HS.fromList . S.invariants $ a
      , liftedIaliases   = HS.fromList . S.ialiases $ a
      , liftedImports    = HS.fromList . S.imports $ a
      , liftedDataDecls  = HS.fromList . S.dataDecls $ a
      , liftedNewtyDecls = HS.fromList . S.newtyDecls $ a
      , liftedAliases    = HS.fromList . S.aliases $ a
      , liftedEaliases   = HS.fromList . S.ealiases $ a
      , liftedEmbeds     = S.embeds a
      , liftedQualifiers = HS.fromList . S.qualifiers $ a
      , liftedDecr       = HS.fromList . S.decr $ a
      , liftedLvars      = S.lvars a
      , liftedAutois     = S.autois a
      , liftedAutosize   = S.autosize a
      , liftedCmeasures  = HS.fromList . S.cmeasures $ a
      , liftedImeasures  = HS.fromList . S.imeasures $ a
      , liftedClasses    = HS.fromList . S.classes $ a
      , liftedClaws      = HS.fromList . S.claws $ a
      , liftedRinstance  = HS.fromList . S.rinstance $ a
      , liftedIlaws      = HS.fromList . S.ilaws $ a
      , liftedDvariance  = HS.fromList . S.dvariance $ a
      , liftedBounds     = S.bounds a
      , liftedDefs       = S.defs a
      , liftedAxeqs      = HS.fromList . S.axeqs $ a
      }


-- | A newtype wrapper around a 'Module' which:
--
-- * Allows a 'Module' to be serialised (i.e. it has a 'Binary' instance)
-- * It tries to use stable comparison and equality under the hood.
--
newtype StableModule = 
  StableModule { unStableModule :: Module } 
  deriving Generic

instance Hashable StableModule where
  hashWithSalt s (StableModule mdl) = hashWithSalt s (moduleStableString mdl)

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

-- | The /target/ dependencies that concur to the creation of a 'TargetSpec' and a 'LiftedSpec'.
newtype TargetDependencies =
  TargetDependencies { getDependencies :: HashMap StableModule LiftedSpec }
  deriving (Eq, Show, Semigroup, Monoid, Generic)
  deriving Binary via Generically TargetDependencies

{------------------------------------------------------------------------------------------------------------
 Utility functions
------------------------------------------------------------------------------------------------------------}

debugShowModule :: Module -> String
debugShowModule m = showSDocUnsafe $
                     text "Module { unitId = " <+> ppr (moduleUnitId m)
                 <+> text ", name = " <+> ppr (moduleName m) 
                 <+> text " }"

isPLEVar :: TargetSpec -> Var -> Bool 
isPLEVar sp x = M.member x (S.gsAutoInst (gsRefl sp)) 

isExportedVar :: TargetSrc -> Var -> Bool
isExportedVar src v = n `elemNameSet` ns
  where
    n                = getName v
    ns               = gsExports src

{------------------------------------------------------------------------------------------------------------
 Stubbed interface for creating and manipulating specs (replaces 'Language.Haskell.Liquid.Bare').
------------------------------------------------------------------------------------------------------------}

-- | @makeTargetSpec@ constructs the @TargetSpec@ and then validates it using @validateTargetSpec@.
-- Upon success, the 'TargetSpec' and the 'LiftedSpec' are returned.
makeTargetSpec :: Config
               -> LogicMap
               -> TargetSrc
               -> BareSpec
               -> TargetDependencies
               -> Either [Error] (TargetSpec, LiftedSpec)
makeTargetSpec cfg lmap targetSrc bareSpec dependencies = do
  -- Check that our input 'BareSpec' doesn't contain duplicates.
  validatedBareSpec <- Bare.checkBareSpec (giTargetMod targetSrc) (review bareSpecIso bareSpec)
  let allSpecs = 
        toLegacyTarget validatedBareSpec : (map toLegacyDep . M.toList . getDependencies $ dependencies)
  pure $ view targetSpecGetter (Bare.makeGhcSpec cfg (review targetSrcIso targetSrc) lmap allSpecs)
  where
    toLegacyDep :: (StableModule, LiftedSpec) -> (ModName, S.BareSpec)
    toLegacyDep (sm, ls) = (ModName SrcImport (moduleName . unStableModule $ sm), unsafeFromLiftedSpec ls)

    toLegacyTarget :: S.BareSpec -> (ModName, S.BareSpec)
    toLegacyTarget validatedSpec = (giTargetMod targetSrc, validatedSpec)

-- This is a temporary internal function that we use to convert the input dependencies into a format
-- suitable for 'makeGhcSpec'.
unsafeFromLiftedSpec :: LiftedSpec -> S.BareSpec
unsafeFromLiftedSpec a = S.Spec
  { S.measures   = HS.toList . liftedMeasures $ a
  , S.impSigs    = HS.toList . liftedImpSigs $ a
  , S.expSigs    = HS.toList . liftedExpSigs $ a
  , S.asmSigs    = HS.toList . liftedAsmSigs $ a
  , S.sigs       = HS.toList . liftedSigs $ a
  , S.localSigs  = mempty
  , S.reflSigs   = mempty
  , S.invariants = HS.toList . liftedInvariants $ a
  , S.ialiases   = HS.toList . liftedIaliases $ a
  , S.imports    = HS.toList . liftedImports $ a
  , S.dataDecls  = HS.toList . liftedDataDecls $ a
  , S.newtyDecls = HS.toList . liftedNewtyDecls $ a
  , S.includes   = mempty
  , S.aliases    = HS.toList . liftedAliases $ a
  , S.ealiases   = HS.toList . liftedEaliases $ a
  , S.embeds     = liftedEmbeds a
  , S.qualifiers = HS.toList . liftedQualifiers $ a
  , S.decr       = HS.toList . liftedDecr $ a
  , S.lvars      = liftedLvars a
  , S.lazy       = mempty
  , S.reflects   = mempty
  , S.autois     = liftedAutois a
  , S.hmeas      = mempty
  , S.hbounds    = mempty
  , S.inlines    = mempty
  , S.ignores    = mempty
  , S.autosize   = liftedAutosize a
  , S.pragmas    = mempty
  , S.cmeasures  = HS.toList . liftedCmeasures $ a
  , S.imeasures  = HS.toList . liftedImeasures $ a
  , S.classes    = HS.toList . liftedClasses $ a
  , S.claws      = HS.toList . liftedClaws $ a
  , S.termexprs  = mempty
  , S.rinstance  = HS.toList . liftedRinstance $ a
  , S.ilaws      = HS.toList . liftedIlaws $ a
  , S.dvariance  = HS.toList . liftedDvariance $ a
  , S.bounds     = liftedBounds a
  , S.defs       = liftedDefs a
  , S.axeqs      = HS.toList . liftedAxeqs $ a
  }
