{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveDataTypeable        #-}

module Language.Fixpoint.Bitvector
       ( -- * Sizes 
         BvSize (..)

         -- * Operators
       , BvOp (..)

         -- * BitVector Sort Constructor
       , mkSort 

         -- * BitVector Expression Constructor 
       , eOp

       ) where

import qualified Data.Text as T
import Language.Fixpoint.Types
import Language.Fixpoint.Names
import GHC.Generics         (Generic)
import Data.Typeable        (Typeable)
import Data.Generics        (Data)

data Bv     = Bv BvSize String 

data BvSize = S32   | S64
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

data BvOp   = BvAnd | BvOr
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Construct the bitvector `Sort` from its `BvSize`

mkSort :: BvSize -> Sort
mkSort s = fApp (Left bvTyCon) [sizeSort s]

-- | Construct an `Expr` using a raw string, e.g. (Bv S32 "#x02000000")
instance Expression Bv where
  expr (Bv sz v) = ECon $ L (T.pack v) (mkSort sz)

-- | Apply some bitvector operator to a list of arguments

eOp :: BvOp -> [Expr] -> Expr
eOp o es = EApp (opName o) es


--------------------------------------------------------------------

opName :: BvOp -> LocSymbol
opName BvAnd = dummyLoc bvAndName
opName BvOr  = dummyLoc bvOrName

sizeSort     = (`FApp` []) . sizeTC
sizeTC       = symbolFTycon . dummyLoc . sizeName 
sizeName S32 = size32Name
sizeName S64 = size64Name

bvTyCon      = symbolFTycon $ dummyLoc bitVecName

-- s32TyCon     = symbolFTycon $ dummyLoc size32Name 
-- s64TyCon     = symbolFTycon $ dummyLoc size64Name

