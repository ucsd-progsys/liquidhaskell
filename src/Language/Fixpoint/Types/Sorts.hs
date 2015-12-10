{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}

-- | This module contains the data types, operations and
--   serialization functions for representing Fixpoint's
--   implication (i.e. subtyping) and well-formedness
--   constraints in Haskell. The actual constraint
--   solving is done by the `fixpoint.native` which
--   is written in Ocaml.

module Language.Fixpoint.Types.Sorts (

  -- * Embedding to Fixpoint Types
     Sort (..), FTycon, TCEmb
  , sortFTycon
  , intFTyCon, boolFTyCon, realFTyCon, numFTyCon  -- TODO: hide these

  , intSort, realSort, propSort, boolSort, strSort, funcSort
  , listFTyCon
  , isListTC
  , fTyconSymbol, symbolFTycon, fTyconSort
  , fApp, fAppTC
  , fObj

  ) where

import           Debug.Trace               (trace)
import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)

import           Data.Hashable
import           Data.List                 (partition, foldl', sort, sortBy)
import           Data.String
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           GHC.Conc                  (getNumProcessors)
import           Control.DeepSeq
import           Data.Maybe                (isJust, mapMaybe, listToMaybe, fromMaybe)
import           Text.Printf               (printf)
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Utils.Misc
import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ
import           Data.Array                hiding (indices)
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S


newtype FTycon = TC LocSymbol deriving (Eq, Ord, Show, Data, Typeable, Generic)
type TCEmb a   = M.HashMap a FTycon

intFTyCon, boolFTyCon, realFTyCon, funcFTyCon, numFTyCon, strFTyCon, propFTyCon, listFTyCon :: FTycon
intFTyCon  = TC $ dummyLoc "int"
boolFTyCon = TC $ dummyLoc "bool"
realFTyCon = TC $ dummyLoc "real"
numFTyCon  = TC $ dummyLoc "num"
funcFTyCon = TC $ dummyLoc "function"
strFTyCon  = TC $ dummyLoc strConName
propFTyCon = TC $ dummyLoc propConName
listFTyCon = TC $ dummyLoc listConName

isListConName :: LocSymbol -> Bool
isListConName x = c == listConName || c == listLConName --"List"
  where
    c           = val x

isListTC :: FTycon -> Bool
isListTC (TC z) = isListConName z

fTyconSymbol :: FTycon -> Located Symbol
fTyconSymbol (TC s) = s

symbolFTycon :: LocSymbol -> FTycon
symbolFTycon c
  | isListConName c
  = TC $ fmap (const listConName) c
  | otherwise
  = TC c

fApp :: Sort -> [Sort] -> Sort
fApp = foldl' FApp

fAppTC :: FTycon -> [Sort] -> Sort
fAppTC = fApp . fTyconSort

fApp' :: Sort -> ListNE Sort
fApp' = go []
  where
    go acc (FApp t1 t2) = go (t2 : acc) t1
    go acc t            = t : acc

fObj :: LocSymbol -> Sort
fObj = fTyconSort . TC

sortFTycon :: Sort -> Maybe FTycon
sortFTycon FInt    = Just intFTyCon
sortFTycon FReal   = Just realFTyCon
sortFTycon FNum    = Just numFTyCon
sortFTycon (FTC c) = Just c
sortFTycon _       = Nothing

----------------------------------------------------------------------
------------------------------- Sorts --------------------------------
----------------------------------------------------------------------

data Sort = FInt
          | FReal
          | FNum                 -- ^ numeric kind for Num tyvars
          | FFrac                -- ^ numeric kind for Fractional tyvars
          | FObj  Symbol         -- ^ uninterpreted type
          | FVar  !Int           -- ^ fixpoint type variable
          | FFunc !Int ![Sort]   -- ^ type-var arity, in-ts ++ [out-t]
          | FTC   FTycon
          | FApp  Sort Sort      -- ^ constructed type
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

{-@ FFunc :: Nat -> ListNE Sort -> Sort @-}

instance Hashable Sort

newtype Sub = Sub [(Int, Sort)] deriving (Generic)

instance Fixpoint Sort where
  toFix = toFixSort

toFixSort :: Sort -> Doc
toFixSort (FVar i)     = text "@"   <> parens (toFix i)
toFixSort FInt         = text "int"
toFixSort FReal        = text "real"
toFixSort FFrac        = text "frac"
toFixSort (FObj x)     = toFix x
toFixSort FNum         = text "num"
toFixSort (FFunc n ts) = text "func" <> parens (toFix n <> text ", " <> toFix ts)
toFixSort (FTC c)      = toFix c
toFixSort t@(FApp _ _) = toFixFApp (fApp' t)

toFixFApp            :: ListNE Sort -> Doc
toFixFApp [t]        = toFixSort t
toFixFApp [FTC c, t]
  | isListTC c       = brackets $ toFixSort t
toFixFApp ts         = parens $ intersperse space (toFixSort <$> ts)

instance Fixpoint FTycon where
  toFix (TC s)       = toFix s

-------------------------------------------------------------------------
-- | Exported Basic Sorts -----------------------------------------------
-------------------------------------------------------------------------

numSort, boolSort, intSort, propSort, realSort, strSort, funcSort :: Sort
boolSort = fTyconSort boolFTyCon
strSort  = fTyconSort strFTyCon
intSort  = fTyconSort intFTyCon
realSort = fTyconSort realFTyCon
propSort = fTyconSort propFTyCon
numSort  = fTyconSort numFTyCon
funcSort = fTyconSort funcFTyCon

fTyconSort :: FTycon -> Sort
fTyconSort c
  | c == intFTyCon  = FInt
  | c == realFTyCon = FReal
  | c == numFTyCon  = FNum
  | otherwise       = FTC c

------------------------------------------------------------------------
sortSubst                  :: M.HashMap Symbol Sort -> Sort -> Sort
------------------------------------------------------------------------
sortSubst θ t@(FObj x)   = fromMaybe t (M.lookup x θ)
sortSubst θ (FFunc n ts) = FFunc n (sortSubst θ <$> ts)
sortSubst θ (FApp t1 t2) = FApp (sortSubst θ t1) (sortSubst θ t2)
sortSubst _  t           = t
