{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Fixpoint.Types.Spans (

  -- * Concrete Location Type
    SourcePos(..)
  , SourceName
  , SrcSpan (..)
  , Pos
  , predPos
  , safePos
  , safeSourcePos
  , succPos
  , unPos

  -- * Located Values
  , Loc (..)
  , Located (..)

  -- * Constructing spans
  , dummySpan
  , panicSpan
  , locAt
  , dummyLoc
  , dummyPos
  , atLoc
  , toSourcePos

  -- * Destructing spans
  , sourcePosElts
  , srcLine 
  ) where

-- import           Control.Exception
import           Control.DeepSeq
-- import qualified Control.Monad.Error           as E
import           Data.Serialize                (Serialize (..))
import           Data.Generics                 (Data)
import           Data.Hashable
import           Data.Typeable
import           Data.String
import qualified Data.Binary                   as B
import           GHC.Generics                  (Generic)
import           Language.Fixpoint.Types.PrettyPrint
-- import           Language.Fixpoint.Misc
import           Text.Megaparsec.Pos
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
-- import           Debug.Trace


-----------------------------------------------------------------------
-- | Located Values ---------------------------------------------------
-----------------------------------------------------------------------

class Loc a where
  srcSpan :: a -> SrcSpan

-----------------------------------------------------------------------
-- Additional (orphan) instances for megaparsec's Pos type ------------
-----------------------------------------------------------------------

instance B.Binary Pos where
  put = B.put . unPos
  get = mkPos <$> B.get

instance Serialize Pos where
  put = put . unPos
  get = mkPos <$> get

instance Hashable Pos where
  hashWithSalt i = hashWithSalt i . unPos

instance PrintfArg Pos where
  formatArg = formatArg . unPos
  parseFormat = parseFormat . unPos

-- | Computes, safely, the predecessor of a 'Pos' value, stopping at 1.
predPos :: Pos -> Pos
predPos pos =
  mkPos $
  case unPos pos of
    1 -> 1
    atLeastTwo -> atLeastTwo - 1

-- | Computes the successor of a 'Pos' value.
succPos :: Pos -> Pos
succPos pos =
  mkPos $ unPos pos + 1

-- | Create, safely, as position. If a non-positive number is given,
-- we use 1.
--
safePos :: Int -> Pos
safePos i
  | i <= 0    = mkPos 1
  | otherwise = mkPos i

-- | Create a source position from integers, using 1 in case of
-- non-positive numbers.
safeSourcePos :: FilePath -> Int -> Int -> SourcePos
safeSourcePos file line col =
  SourcePos file (safePos line) (safePos col)

-----------------------------------------------------------------------
-- | Retrofitting instances to SourcePos ------------------------------
-----------------------------------------------------------------------

instance B.Binary SourcePos where
  put = B.put . ofSourcePos
  get = toSourcePos <$> B.get

instance Serialize SourcePos where
  put = put . ofSourcePos
  get = toSourcePos <$> get

instance PPrint SourcePos where
  pprintTidy _ = ppSourcePos

instance Hashable SourcePos where
  hashWithSalt i   = hashWithSalt i . sourcePosElts

-- | This is a compatibility type synonym for megaparsec vs. parsec.
type SourceName = FilePath

-- | This is a compatibility type synonym for megaparsec vs. parsec.
type Line = Pos

-- | This is a compatibility type synonym for megaparsec vs. parsec.
type Column = Pos

ofSourcePos :: SourcePos -> (SourceName, Line, Column)
ofSourcePos p = (f, l, c)
  where
   f = sourceName   p
   l = sourceLine   p
   c = sourceColumn p

toSourcePos :: (SourceName, Line, Column) -> SourcePos
toSourcePos (f, l, c) = SourcePos f l c

sourcePosElts :: SourcePos -> (SourceName, Line, Column)
sourcePosElts = ofSourcePos

ppSourcePos :: SourcePos -> Doc
ppSourcePos z = text (printf "%s:%d:%d" f l c)
  where
    (f,l,c) = sourcePosElts $ z

instance Fixpoint SourcePos where
  toFix = text . show


data Located a = Loc { loc  :: !SourcePos -- ^ Start Position
                     , locE :: !SourcePos -- ^ End Position
                     , val  :: !a
                     } deriving (Data, Typeable, Generic)

instance Loc (Located a) where
  srcSpan (Loc l l' _) = SS l l'


instance (NFData a) => NFData (Located a)

instance Fixpoint a => Fixpoint (Located a) where
  toFix = toFix . val

instance Functor Located where
  fmap f (Loc l l' x) =  Loc l l' (f x)

instance Foldable Located where
  foldMap f (Loc _ _ x) = f x

instance Traversable Located where
  traverse f (Loc l l' x) = Loc l l' <$> f x

instance Show a => Show (Located a) where
  show (Loc l l' x)
    | l == l' && l == dummyPos "Fixpoint.Types.dummyLoc" = show x ++ " (dummyLoc)"
    | otherwise  = show x ++ " defined at: " ++ render (ppSrcSpan (SS l l'))

instance PPrint a => PPrint (Located a) where
  pprintTidy k (Loc _ _ x) = pprintTidy k x

instance Eq a => Eq (Located a) where
  (Loc _ _ x) == (Loc _ _ y) = x == y

instance Ord a => Ord (Located a) where
  compare x y = compare (val x) (val y)

instance (B.Binary a) => B.Binary (Located a)

instance Hashable a => Hashable (Located a) where
  hashWithSalt i = hashWithSalt i . val

instance (IsString a) => IsString (Located a) where
  fromString = dummyLoc . fromString

srcLine :: (Loc a) => a -> Pos
srcLine = sourceLine . sp_start . srcSpan

-----------------------------------------------------------------------
-- | A Reusable SrcSpan Type ------------------------------------------
-----------------------------------------------------------------------

data SrcSpan = SS { sp_start :: !SourcePos
                  , sp_stop  :: !SourcePos}
                 deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance Serialize SrcSpan

instance PPrint SrcSpan where
  pprintTidy _ = ppSrcSpan

-- ppSrcSpan_short z = parens
--                   $ text (printf "file %s: (%d, %d) - (%d, %d)" (takeFileName f) l c l' c')
--   where
--     (f,l ,c )     = sourcePosElts $ sp_start z
--     (_,l',c')     = sourcePosElts $ sp_stop  z

ppSrcSpan :: SrcSpan -> Doc
ppSrcSpan z       = text (printf "%s:%d:%d-%d:%d" f l c l' c')
                -- parens $ text (printf "file %s: (%d, %d) - (%d, %d)" (takeFileName f) l c l' c')
  where
    (f,l ,c )     = sourcePosElts $ sp_start z
    (_,l',c')     = sourcePosElts $ sp_stop  z


instance Hashable SrcSpan where
  hashWithSalt i z = hashWithSalt i (sp_start z, sp_stop z)

instance Loc SrcSpan where 
  srcSpan x = x 

instance Loc () where
  srcSpan _ = dummySpan

instance Loc SourcePos where 
  srcSpan l = SS l l

dummySpan :: SrcSpan
dummySpan = panicSpan ""

panicSpan :: String -> SrcSpan
panicSpan s = SS l l
  where l = initialPos s

-- atLoc :: Located a -> b -> Located b
-- atLoc (Loc l l' _) = Loc l l'

atLoc :: (Loc l) => l -> b -> Located b
atLoc z x   = Loc l l' x
  where
    SS l l' = srcSpan z


locAt :: String -> a -> Located a
locAt s  = Loc l l
  where
    l    = dummyPos s

dummyLoc :: a -> Located a
dummyLoc = Loc l l
  where
    l    = dummyPos "Fixpoint.Types.dummyLoc"

dummyPos   :: FilePath -> SourcePos
dummyPos = initialPos
