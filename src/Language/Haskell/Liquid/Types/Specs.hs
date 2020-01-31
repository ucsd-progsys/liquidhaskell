-- | This module contains the top-level structures that hold 
--   information about specifications.

{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE RecordWildCards            #-}

module Language.Haskell.Liquid.Types.Specs where 

import           GHC.Generics
import qualified Data.Binary             as B
import qualified Language.Fixpoint.Types as F
import qualified Data.HashSet            as S
import qualified Data.HashMap.Strict     as M
import           Language.Haskell.Liquid.Types.Types 
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds 
import           Language.Haskell.Liquid.GHC.API 
import           Text.PrettyPrint.HughesPJ              (text, (<+>)) 

-------------------------------------------------------------------------
-- | GHC Information:  Code & Spec --------------------------------------
-------------------------------------------------------------------------

-- | The following is the overall type for /specifications/ obtained from
-- parsing the target source and dependent libraries

data GhcInfo = GI
  { giSrc       :: !GhcSrc  
  , giSpec      :: !GhcSpec               -- ^ All specification information for module
  }

data GhcSrc = Src 
  { giIncDir    :: !FilePath              -- ^ Path for LH include/prelude directory
  , giTarget    :: !FilePath              -- ^ Source file for module
  , giTargetMod :: !ModName               -- ^ Name for module
  , giCbs       :: ![CoreBind]            -- ^ Source Code
  , gsTcs       :: ![TyCon]               -- ^ All used Type constructors
  , gsCls       :: !(Maybe [ClsInst])     -- ^ Class instances?
  , giDerVars   :: !(S.HashSet Var)       -- ^ Binders created by GHC eg dictionaries
  , giImpVars   :: ![Var]                 -- ^ Binders that are _read_ in module (but not defined?)
  , giDefVars   :: ![Var]                 -- ^ (Top-level) binders that are _defined_ in module
  , giUseVars   :: ![Var]                 -- ^ Binders that are _read_ in module
  , gsExports   :: !NameSet               -- ^ `Name`s exported by the module being verified
  , gsFiTcs     :: ![TyCon]               -- ^ Family instance TyCons 
  , gsFiDcs     :: ![(F.Symbol, DataCon)] -- ^ Family instance DataCons 
  , gsPrimTcs   :: ![TyCon]               -- ^ Primitive GHC TyCons (from TysPrim.primTyCons)
  , gsQualImps  :: !QImports              -- ^ Map of qualified imports
  , gsAllImps   :: !(S.HashSet F.Symbol)  -- ^ Set of _all_ imported modules
  , gsTyThings  :: ![TyThing]             -- ^ All the @TyThing@s known to GHC
  }

-- | @QImports@ is a map of qualified imports.
data QImports = QImports 
  { qiModules :: !(S.HashSet F.Symbol)            -- ^ All the modules that are imported qualified
  , qiNames   :: !(M.HashMap F.Symbol [F.Symbol]) -- ^ Map from qualification to full module name
  }

data GhcSpec = SP 
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
  , gsLSpec  :: !BareSpec               -- ^ Lifted specification for the target module
  }

instance HasConfig GhcSpec where
  getConfig = gsConfig

instance HasConfig GhcInfo where
  getConfig = getConfig . giSpec

data GhcSpecVars = SpVar 
  { gsTgtVars    :: ![Var]                        -- ^ Top-level Binders To Verify (empty means ALL binders)
  , gsIgnoreVars :: !(S.HashSet Var)              -- ^ Top-level Binders To NOT Verify (empty means ALL binders)
  , gsLvars      :: !(S.HashSet Var)              -- ^ Variables that should be checked "lazily" in the environment they are used
  , gsCMethods   :: ![Var]                        -- ^ Refined Class methods 
  }

data GhcSpecQual = SpQual 
  { gsQualifiers :: ![F.Qualifier]                -- ^ Qualifiers in Source/Spec files e.g tests/pos/qualTest.hs
  , gsRTAliases  :: ![F.Located SpecRTAlias]      -- ^ Refinement type aliases (only used for qualifiers)
  -- REBARE: , giHqFiles   :: ![FilePath]         -- ^ Imported .hqual files
  }

data GhcSpecSig = SpSig 
  { gsTySigs   :: ![(Var, LocSpecType)]           -- ^ Asserted Reftypes
  , gsAsmSigs  :: ![(Var, LocSpecType)]           -- ^ Assumed Reftypes
  , gsInSigs   :: ![(Var, LocSpecType)]           -- ^ Auto generated Signatures
  , gsNewTypes :: ![(TyCon, LocSpecType)]         -- ^ Mapping of 'newtype' type constructors with their refined types.
  , gsDicts    :: !(DEnv Var LocSpecType)            -- ^ Refined Classes from Instances 
  , gsMethods  :: ![(Var, MethodType LocSpecType)]   -- ^ Refined Classes from Classes 
  , gsTexprs   :: ![(Var, LocSpecType, [F.Located F.Expr])]  -- ^ Lexicographically ordered expressions for termination
  }

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
  -- REBARE: == gsMeas , gsLits       :: ![(F.Symbol, LocSpecType)]    -- ^ Literals/Constants e.g. datacons: EQ, GT, string lits: "zombie",...
  , gsTcEmbeds   :: !(F.TCEmb TyCon)              -- ^ Embedding GHC Tycons into fixpoint sorts e.g. "embed Set as Set_set" from include/Data/Set.spec
  , gsADTs       :: ![F.DataDecl]                 -- ^ ADTs extracted from Haskell 'data' definitions
  , gsTyconEnv   :: !TyConMap
  }

data GhcSpecTerm = SpTerm 
  { gsStTerm     :: !(S.HashSet Var)              -- ^ Binders to CHECK by structural termination
  , gsAutosize   :: !(S.HashSet TyCon)            -- ^ Binders to IGNORE during termination checking
  , gsLazy       :: !(S.HashSet Var)              -- ^ Binders to IGNORE during termination checking
  , gsDecr       :: ![(Var, [Int])]               -- ^ Lexicographic order of decreasing args (DEPRECATED) 
  , gsNonStTerm  :: !(S.HashSet Var)              -- ^ Binders to CHECK using REFINEMENT-TYPES/termination metrics 
  }

data GhcSpecRefl = SpRefl 
  { gsAutoInst   :: !(M.HashMap Var (Maybe Int))      -- ^ Binders to USE PLE 
  , gsHAxioms    :: ![(Var, LocSpecType, F.Equation)] -- ^ Lifted definitions 
  , gsImpAxioms  :: ![F.Equation]                     -- ^ Axioms from imported reflected functions
  , gsMyAxioms   :: ![F.Equation]                     -- ^ Axioms from my reflected functions
  , gsReflects   :: ![Var]                            -- ^ Binders for reflected functions
  , gsLogicMap   :: !LogicMap
  , gsWiredReft  :: ![Var]
  }

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
type BareSpec      = Spec    LocBareType F.LocSymbol
type BareMeasure   = Measure LocBareType F.LocSymbol
type BareDef       = Def     LocBareType F.LocSymbol
type SpecMeasure   = Measure LocSpecType DataCon
    
instance B.Binary BareSpec

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

instance (Show ty, Show bndr, F.PPrint ty, F.PPrint bndr) => F.PPrint (Spec ty bndr) where
    pprintTidy k sp = text "dataDecls = " <+> pprintTidy k  (dataDecls sp)


isExportedVar :: GhcSrc -> Var -> Bool
isExportedVar info v = n `elemNameSet` ns
  where
    n                = getName v
    ns               = gsExports info

isPLEVar :: GhcSpec -> Var -> Bool 
isPLEVar sp x = M.member x (gsAutoInst (gsRefl sp)) 


