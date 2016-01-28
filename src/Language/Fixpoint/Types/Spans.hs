{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Fixpoint.Types.Spans (

  -- * Concrete Location Type
    SourcePos
  , SrcSpan (..)

  -- * Located Values
  , Loc (..)
  , Located (..)

  -- * Constructing spans
  , dummySpan
  , locAt
  , dummyLoc
  , dummyPos
  , atLoc 

  -- * Destructing spans
  , sourcePosElts
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
import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
-- import           Debug.Trace

-----------------------------------------------------------------------
-- | Located Values ---------------------------------------------------
-----------------------------------------------------------------------

class Loc a where
  srcSpan :: a -> SrcSpan

-----------------------------------------------------------------------
-- | Retrofitting instances to SourcePos ------------------------------
-----------------------------------------------------------------------

instance NFData SourcePos where
  rnf = rnf . ofSourcePos

instance B.Binary SourcePos where
  put = B.put . ofSourcePos
  get = toSourcePos <$> B.get

instance Serialize SourcePos where
  put = put . ofSourcePos
  get = toSourcePos <$> get

instance PPrint SourcePos where
  pprint = text . show

instance Hashable SourcePos where
  hashWithSalt i   = hashWithSalt i . sourcePosElts

ofSourcePos :: SourcePos -> (SourceName, Line, Column)
ofSourcePos p = (f, l, c)
  where
   f = sourceName   p
   l = sourceLine   p
   c = sourceColumn p

toSourcePos :: (SourceName, Line, Column) -> SourcePos
toSourcePos (f, l, c) = newPos f l c

sourcePosElts s = (src, line, col)
  where
    src         = sourceName   s
    line        = sourceLine   s
    col         = sourceColumn s

instance Fixpoint SourcePos where
  toFix = text . show


data Located a = Loc { loc  :: !SourcePos -- ^ Start Position
                     , locE :: !SourcePos -- ^ End Position
                     , val  :: a
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
  show (Loc l l' x) = show x ++ " defined from: " ++ show l ++ " to: " ++ show l'

instance PPrint a => PPrint (Located a) where
  pprint (Loc _ _ x) = pprint x

instance Eq a => Eq (Located a) where
  (Loc _ _ x) == (Loc _ _ y) = x == y

instance Ord a => Ord (Located a) where
  compare x y = compare (val x) (val y)

instance (B.Binary a) => B.Binary (Located a)

instance Hashable a => Hashable (Located a) where
  hashWithSalt i = hashWithSalt i . val

instance (IsString a) => IsString (Located a) where
  fromString = dummyLoc . fromString


-----------------------------------------------------------------------
-- | A Reusable SrcSpan Type ------------------------------------------
-----------------------------------------------------------------------

data SrcSpan = SS { sp_start :: !SourcePos
                  , sp_stop  :: !SourcePos}
                 deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance Serialize SrcSpan

instance PPrint SrcSpan where
  pprint = ppSrcSpan

-- ppSrcSpan_short z = parens
--                   $ text (printf "file %s: (%d, %d) - (%d, %d)" (takeFileName f) l c l' c')
--   where
--     (f,l ,c )     = sourcePosElts $ sp_start z
--     (_,l',c')     = sourcePosElts $ sp_stop  z


ppSrcSpan z       = text (printf "%s:%d:%d-%d:%d" f l c l' c')
                -- parens $ text (printf "file %s: (%d, %d) - (%d, %d)" (takeFileName f) l c l' c')
  where
    (f,l ,c )     = sourcePosElts $ sp_start z
    (_,l',c')     = sourcePosElts $ sp_stop  z


instance Hashable SrcSpan where
  hashWithSalt i z = hashWithSalt i (sp_start z, sp_stop z)

dummySpan = SS l l
  where l = initialPos ""

atLoc :: Located a -> b -> Located b
atLoc (Loc l l' _) x = Loc l l' x

locAt :: String -> a -> Located a
locAt s  = Loc l l
  where
    l    = dummyPos s

dummyLoc :: a -> Located a
dummyLoc = Loc l l
  where
    l    = dummyPos "Fixpoint.Types.dummyLoc"

dummyPos   :: String -> SourcePos
dummyPos s = newPos s 0 0
