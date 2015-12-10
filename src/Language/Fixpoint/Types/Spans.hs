{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Fixpoint.Types.Spans (

  -- * Concrete Location Type
    SrcSpan (..)

  -- * Located Values
  , Loc (..)
  , Located (..)

  -- * Constructing spans
  , dummySpan

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
import qualified Data.Binary                   as B
import           GHC.Generics                  (Generic)
import           Language.Fixpoint.Types.PrettyPrint
-- import           Language.Fixpoint.Utils.Misc
import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
-- import           Debug.Trace


class Loc a where
  srcSpan :: a -> SrcSpan

data Located a = Loc { loc  :: !SourcePos -- ^ Start Position
                     , locE :: !SourcePos -- ^ End Position
                     , val  :: a
                     } deriving (Data, Typeable, Generic)

-----------------------------------------------------------------------
-- | Retrofitting instances to SourcePos ------------------------------
-----------------------------------------------------------------------

instance NFData SourcePos where
  rnf = rnf . ofSourcePos

instance B.Binary SourcePos where
  put = B.put . ofSourcePos
  get = toSourcePos <$> B.get

instance Serialize SourcePos where
  put = error "Serialize: SourcePos"
  get = error "Serialize: SourcePos"

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
