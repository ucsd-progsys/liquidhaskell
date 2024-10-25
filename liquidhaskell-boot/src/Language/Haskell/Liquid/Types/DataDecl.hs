{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingVia                #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains types to represent refined data types.

module Language.Haskell.Liquid.Types.DataDecl (

  -- * Parse-time entities describing refined data types
    DataDecl (..)
  , DataName (..), dataNameSymbol
  , DataCtor (..)
  , DataConP (..)
  , HasDataDecl (..), hasDecl
  , DataDeclKind (..)
  , TyConP   (..)

  )
  where

import qualified Liquid.GHC.API as Ghc
import           GHC.Generics
import           Prelude                          hiding  (error)

import           Control.DeepSeq
import           Data.Typeable                          (Typeable)
import           Data.Generics                          (Data)
import qualified Data.Binary                            as B
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ              hiding (first, (<>))
import           Text.Printf

import qualified Language.Fixpoint.Types as F

import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType


--------------------------------------------------------------------------------
-- | Data type refinements
--------------------------------------------------------------------------------
data DataDecl   = DataDecl
  { tycName   :: DataName              -- ^ Type  Constructor Name
  , tycTyVars :: [F.Symbol]            -- ^ Tyvar Parameters
  , tycPVars  :: [PVar BSort]          -- ^ PVar  Parameters
  , tycDCons  :: Maybe [DataCtor]      -- ^ Data Constructors (Nothing is reserved for non-GADT style empty data declarations)
  , tycSrcPos :: !F.SourcePos          -- ^ Source Position
  , tycSFun   :: Maybe SizeFun         -- ^ Default termination measure
  , tycPropTy :: Maybe BareType        -- ^ Type of Ind-Prop
  , tycKind   :: !DataDeclKind         -- ^ User-defined or Auto-lifted
  } deriving (Data, Typeable, Generic)
    deriving Hashable via Generically DataDecl

-- | The name of the `TyCon` corresponding to a `DataDecl`
data DataName
  = DnName !(F.Located LHName)         -- ^ for 'isVanillyAlgTyCon' we can directly use the `TyCon` name
  | DnCon  !(F.Located LHName)         -- ^ for 'FamInst' TyCon we save some `DataCon` name
  deriving (Eq, Ord, Data, Typeable, Generic)

instance Hashable DataName

-- | Data Constructor
data DataCtor = DataCtor
  { dcName   :: F.Located LHName       -- ^ DataCon name
  , dcTyVars :: [F.Symbol]             -- ^ Type parameters
  , dcTheta  :: [BareType]             -- ^ The GHC ThetaType corresponding to DataCon.dataConSig
  , dcFields :: [(F.Symbol, BareType)] -- ^ field-name and field-Type pairs
  , dcResult :: Maybe BareType         -- ^ Possible output (if in GADT form)
  } deriving (Data, Typeable, Generic, Eq)
    deriving Hashable via Generically DataCtor

-- | What kind of `DataDecl` is it?
data DataDeclKind
  = DataUser           -- ^ User defined data-definitions         (should have refined fields)
  | DataReflected      -- ^ Automatically lifted data-definitions (do not have refined fields)
  deriving (Eq, Data, Typeable, Generic, Show)
  deriving Hashable via Generically DataDeclKind

data HasDataDecl
  = NoDecl  (Maybe SizeFun)
  | HasDecl
  deriving (Show)

instance F.PPrint HasDataDecl where
  pprintTidy _ HasDecl    = text "HasDecl"
  pprintTidy k (NoDecl z) = text "NoDecl" <+> parens (F.pprintTidy k z)

hasDecl :: DataDecl -> HasDataDecl
hasDecl d
  | null (tycDCons d)
  = NoDecl (tycSFun d)
  -- // | Just s <- tycSFun d, null (tycDCons d)
  -- // = NoDecl (Just s)
  | otherwise
  = HasDecl

instance NFData   DataDeclKind
instance B.Binary DataDeclKind
instance B.Binary DataName
instance B.Binary DataCtor
instance B.Binary DataDecl

instance Eq DataDecl where
  d1 == d2 = tycName d1 == tycName d2

instance Ord DataDecl where
  compare d1 d2 = compare (tycName d1) (tycName d2)

instance F.Loc DataCtor where
  srcSpan = F.srcSpan . dcName

instance F.Loc DataDecl where
  srcSpan = srcSpanFSrcSpan . sourcePosSrcSpan . tycSrcPos

instance F.Loc DataName where
  srcSpan (DnName z) = F.srcSpan z
  srcSpan (DnCon  z) = F.srcSpan z


-- | For debugging.
instance Show DataDecl where
  show dd = printf "DataDecl: data = %s, tyvars = %s, sizeFun = %s, kind = %s" -- [at: %s]"
              (show $ tycName   dd)
              (show $ tycTyVars dd)
              (show $ tycSFun   dd)
              (show $ tycKind   dd)


instance Show DataName where
  show (DnName n) =               show (F.val n)
  show (DnCon  c) = "datacon:" ++ show (F.val c)

instance F.PPrint DataName where
  pprintTidy k (DnName n) = F.pprintTidy k (F.val n)
  pprintTidy k (DnCon  n) = F.pprintTidy k (F.val n)

  -- symbol (DnName z) = F.suffixSymbol "DnName" (F.val z)
  -- symbol (DnCon  z) = F.suffixSymbol "DnCon"  (F.val z)

dataNameSymbol :: DataName -> F.Located LHName
dataNameSymbol (DnName z) = z
dataNameSymbol (DnCon  z) = z

-- TODO: just use Located instead of dc_loc, dc_locE
data DataConP = DataConP
  { dcpLoc        :: !F.SourcePos
  , dcpCon        :: !Ghc.DataCon            -- ^ Corresponding GHC DataCon
  , dcpFreeTyVars :: ![RTyVar]               -- ^ Type parameters
  , dcpFreePred   :: ![PVar RSort]           -- ^ Abstract Refinement parameters
  , dcpTyConstrs  :: ![SpecType]             -- ^ ? Class constraints (via `dataConStupidTheta`)
  , dcpTyArgs     :: ![(F.Symbol, SpecType)] -- ^ Value parameters
  , dcpTyRes      :: !SpecType               -- ^ Result type
  , dcpIsGadt     :: !Bool                   -- ^ Was this specified in GADT style (if so, DONT use function names as fields)
  , dcpModule     :: !F.Symbol               -- ^ Which module was this defined in
  , dcpLocE       :: !F.SourcePos
  } deriving (Generic, Data, Typeable)

-- | [NOTE:DataCon-Data] for each 'DataConP' we also
--   store the type of the constructed data. This is
--   *the same as* 'tyRes' for *vanilla* ADTs
--   (e.g. List, Maybe etc.) but may differ for GADTs.
--   For example,
--
--      data Thing a where
--        X  :: Thing Int
--        Y  :: Thing Bool
--
--   Here the 'DataConP' associated with 'X' (resp. 'Y')
--   has 'tyRes' corresponding to 'Thing Int' (resp. 'Thing Bool'),
--   but in both cases, the 'tyData' should be 'Thing a'.
--

instance F.Loc DataConP where
  srcSpan d = F.SS (dcpLoc d) (dcpLocE d)

instance F.PPrint BareType => F.PPrint DataDecl where
  pprintTidy k dd =
    let
      prefix = "data" <+> F.pprint (tycName dd) <+> ppMbSizeFun (tycSFun dd) <+> F.pprint (tycTyVars dd)
    in
      case tycDCons dd of
        Nothing   -> prefix
        Just cons -> prefix <+> "=" $+$ nest 4 (vcat $ [ "|" <+> F.pprintTidy k c | c <- cons ])

instance F.PPrint BareType => F.PPrint DataCtor where
  pprintTidy k (DataCtor c as ths xts t) = F.pprintTidy k c <+> text "::" <+> ppVars k as <+> ppThetas ths <+> ppFields k " ->" xts <+> "->" <+> res
    where
      res         = maybe "*" (F.pprintTidy k) t
      ppThetas [] = empty
      ppThetas ts = parens (hcat $ punctuate ", " (F.pprintTidy k <$> ts)) <+> "=>"

ppMbSizeFun :: Maybe SizeFun -> Doc
ppMbSizeFun Nothing  = ""
ppMbSizeFun (Just z) = F.pprint z

ppVars :: (F.PPrint a) => F.Tidy -> [a] -> Doc
ppVars k as = "forall" <+> hcat (punctuate " " (F.pprintTidy k <$> as)) <+> "."

ppFields :: (F.PPrint k, F.PPrint v) => F.Tidy -> Doc -> [(k, v)] -> Doc
ppFields k sep' kvs = hcat $ punctuate sep' (F.pprintTidy k <$> kvs)

instance F.PPrint SpecType => F.PPrint DataConP where
  pprintTidy k (DataConP _ dc vs ps cs yts t isGadt mname _)
     =  F.pprintTidy k dc
    <+> parens (hsep (punctuate comma (F.pprintTidy k <$> vs)))
    <+> parens (hsep (punctuate comma (F.pprintTidy k <$> ps)))
    <+> parens (hsep (punctuate comma (F.pprintTidy k <$> cs)))
    <+> parens (hsep (punctuate comma (F.pprintTidy k <$> yts)))
    <+> F.pprintTidy k isGadt
    <+> F.pprintTidy k mname
    <+> F.pprintTidy k t

instance F.PPrint SpecType => Show DataConP where
  show = F.showpp

instance F.PPrint Ghc.DataCon where
  pprintTidy _ = text . showPpr

instance Show Ghc.DataCon where
  show = F.showpp
