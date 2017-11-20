{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs                      #-}

-- | This module contains the data types, operations and
--   serialization functions for representing Fixpoint's
--   implication (i.e. subtyping) and well-formedness
--   constraints in Haskell. The actual constraint
--   solving is done by the `fixpoint.native` which
--   is written in Ocaml.

module Language.Fixpoint.Types.Sorts (

  -- * Embedding to Fixpoint Types
    Sort (..)

  , Sub (..)
  , FTycon, TCEmb
  , sortFTycon
  , intFTyCon
  , boolFTyCon
  , realFTyCon
  , numFTyCon
  , strFTyCon
  , setFTyCon
  , mapFTyCon -- TODO: hide these

  , basicSorts, intSort, realSort, boolSort, strSort, funcSort
  , setSort, bitVecSort, mapSort
  , listFTyCon
  , isListTC
  , sizeBv
  , isFirstOrder
  , mappendFTC
  , fTyconSymbol, symbolFTycon, fTyconSort, symbolNumInfoFTyCon
  , fTyconSelfSort
  , fApp
  , fAppTC
  , fObj
  , unFApp
  , unAbs

  , sortSubst
  , functionSort
  , mkFFunc
  , bkFFunc

  , isNumeric, isReal, isString, isPolyInst

  -- * User-defined ADTs
  , DataField (..)
  , DataCtor (..)
  , DataDecl (..)

  ) where

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)

import           Data.Monoid               ()
import           Data.Hashable
import           Data.List                 (foldl')
import           Control.DeepSeq
import           Data.Maybe                (fromMaybe)
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ
import qualified Data.HashMap.Strict       as M


data FTycon   = TC LocSymbol TCInfo deriving (Ord, Show, Data, Typeable, Generic)
type TCEmb a  = M.HashMap a Sort -- FTycon

-- instance Show FTycon where
--   show (TC s _) = show (val s)

instance Symbolic FTycon where
  symbol (TC s _) = symbol s

instance Eq FTycon where
  (TC s _) == (TC s' _) = val s == val s'

data TCInfo = TCInfo { tc_isNum :: Bool, tc_isReal :: Bool, tc_isString :: Bool }
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

mappendFTC :: FTycon -> FTycon -> FTycon
mappendFTC (TC x i1) (TC _ i2) = TC x (mappend i1 i2)

instance Monoid TCInfo where
  mempty                                          = TCInfo defNumInfo defRealInfo defStrInfo
  mappend (TCInfo i1 i2 i3)  (TCInfo i1' i2' i3') = TCInfo (i1 || i1') (i2 || i2') (i3 || i3')

defTcInfo, numTcInfo, realTcInfo, strTcInfo :: TCInfo
defTcInfo  = TCInfo defNumInfo defRealInfo defStrInfo
numTcInfo  = TCInfo True       defRealInfo defStrInfo
realTcInfo = TCInfo True       True        defStrInfo
strTcInfo  = TCInfo defNumInfo defRealInfo True

defNumInfo, defRealInfo, defStrInfo :: Bool
defNumInfo  = False
defRealInfo = False
defStrInfo  = False

charFTyCon, intFTyCon, boolFTyCon, realFTyCon, funcFTyCon, numFTyCon :: FTycon
strFTyCon, listFTyCon, mapFTyCon, setFTyCon :: FTycon
intFTyCon  = TC (dummyLoc "int"      ) numTcInfo
boolFTyCon = TC (dummyLoc "bool"     ) defTcInfo
realFTyCon = TC (dummyLoc "real"     ) realTcInfo
numFTyCon  = TC (dummyLoc "num"      ) numTcInfo
funcFTyCon = TC (dummyLoc "function" ) defTcInfo
strFTyCon  = TC (dummyLoc strConName ) strTcInfo
listFTyCon = TC (dummyLoc listConName) defTcInfo
charFTyCon = TC (dummyLoc "Char"     ) defTcInfo
setFTyCon  = TC (dummyLoc setConName ) defTcInfo
mapFTyCon  = TC (dummyLoc mapConName ) defTcInfo

isListConName :: LocSymbol -> Bool
isListConName x = c == listConName || c == listLConName --"List"
  where
    c           = val x

isListTC :: FTycon -> Bool
isListTC (TC z _) = isListConName z

sizeBv :: FTycon -> Maybe Int
sizeBv tc
  | s == size32Name = Just 32
  | s == size64Name = Just 64
  | otherwise       = Nothing
  where
    s               = val $ fTyconSymbol tc

fTyconSymbol :: FTycon -> Located Symbol
fTyconSymbol (TC s _) = s

symbolNumInfoFTyCon :: LocSymbol -> Bool -> Bool -> FTycon
symbolNumInfoFTyCon c isNum isReal
  | isListConName c
  = TC (fmap (const listConName) c) tcinfo
  | otherwise
  = TC c tcinfo
  where
    tcinfo = defTcInfo{tc_isNum = isNum, tc_isReal = isReal}



symbolFTycon :: LocSymbol -> FTycon
symbolFTycon c = symbolNumInfoFTyCon c defNumInfo defRealInfo

fApp :: Sort -> [Sort] -> Sort
fApp = foldl' FApp

fAppTC :: FTycon -> [Sort] -> Sort
fAppTC = fApp . fTyconSort

fTyconSelfSort :: FTycon -> Int -> Sort
fTyconSelfSort c n = fAppTC c [FVar i | i <- [0..(n - 1)]]

-- | fApp' (FApp (FApp "Map" key) val) ===> ["Map", key, val]
--   That is, `fApp'` is used to split a type application into
--   the FTyCon and its args.

unFApp :: Sort -> ListNE Sort
unFApp = go []
  where
    go acc (FApp t1 t2) = go (t2 : acc) t1
    go acc t            = t : acc

unAbs :: Sort -> Sort
unAbs (FAbs _ s) = unAbs s
unAbs s          = s

fObj :: LocSymbol -> Sort
fObj = fTyconSort . (`TC` defTcInfo)

sortFTycon :: Sort -> Maybe FTycon
sortFTycon FInt    = Just intFTyCon
sortFTycon FReal   = Just realFTyCon
sortFTycon FNum    = Just numFTyCon
sortFTycon (FTC c) = Just c
sortFTycon _       = Nothing


functionSort :: Sort -> Maybe ([Int], [Sort], Sort)
functionSort s
  | null is && null ss
  = Nothing
  | otherwise
  = Just (is, ss, r)
  where
    (is, ss, r)            = go [] [] s
    go vs ss (FAbs i t)    = go (i:vs) ss t
    go vs ss (FFunc s1 s2) = go vs (s1:ss) s2
    go vs ss t             = (reverse vs, reverse ss, t)

--------------------------------------------------------------------------------
-- | Sorts ---------------------------------------------------------------------
--------------------------------------------------------------------------------
data Sort = FInt
          | FReal
          | FNum                 -- ^ numeric kind for Num tyvars
          | FFrac                -- ^ numeric kind for Fractional tyvars
          | FObj  !Symbol        -- ^ uninterpreted type
          | FVar  !Int           -- ^ fixpoint type variable
          | FFunc !Sort !Sort    -- ^ function
          | FAbs  !Int !Sort     -- ^ type-abstraction
          | FTC   !FTycon
          | FApp  !Sort !Sort    -- ^ constructed type
            deriving (Eq, Ord, Show, Data, Typeable, Generic)

data DataField = DField
  { dfName :: !LocSymbol          -- ^ Field Name
  , dfSort :: !Sort               -- ^ Field Sort
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)

data DataCtor = DCtor
  { dcName   :: !LocSymbol        -- ^ Ctor Name
  , dcFields :: ![DataField]      -- ^ Ctor Fields
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)

data DataDecl = DDecl
  { ddTyCon :: !FTycon            -- ^ Name of defined datatype
  , ddVars  :: !Int               -- ^ Number of type variables
  , ddCtors :: [DataCtor]         -- ^ Datatype Ctors
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance Symbolic DataDecl where
  symbol = symbol . ddTyCon

instance Symbolic DataField where
  symbol = val . dfName

instance Symbolic DataCtor where
  symbol = val . dcName

isFirstOrder, isFunction :: Sort -> Bool
isFirstOrder (FFunc sx s) = not (isFunction sx) && isFirstOrder s
isFirstOrder (FAbs _ s)   = isFirstOrder s
isFirstOrder (FApp s1 s2) = (not $ isFunction s1) && (not $ isFunction s2)
isFirstOrder _            = True

isFunction (FAbs _ s)  = isFunction s
isFunction (FFunc _ _) = True
isFunction _           = False

isNumeric :: Sort -> Bool
isNumeric FInt           = True
isNumeric (FApp s _)     = isNumeric s
isNumeric (FTC (TC _ i)) = tc_isNum i
isNumeric (FAbs _ s)     = isNumeric s
isNumeric _              = False

isReal :: Sort -> Bool
isReal FReal          = True
isReal (FApp s _)     = isReal s
isReal (FTC (TC _ i)) = tc_isReal i
isReal (FAbs _ s)     = isReal s
isReal _              = False


isString :: Sort -> Bool
isString (FApp l c)     = (isList l && isChar c) || isString l
isString (FTC (TC c i)) = (val c == strConName || tc_isString i)
isString (FAbs _ s)     = isString s
isString _              = False

isList :: Sort -> Bool
isList (FTC c) = isListTC c
isList _       = False

isChar :: Sort -> Bool
isChar (FTC c) = c == charFTyCon
isChar _       = False

{-@ FFunc :: Nat -> ListNE Sort -> Sort @-}

mkFFunc :: Int -> [Sort] -> Sort
mkFFunc i ss     = go [0..i-1] ss
  where
    go [] [s]    = s
    go [] (s:ss) = FFunc s $ go [] ss
    go (i:is) ss = FAbs  i $ go is ss
    go _ _       = error "cannot happen"

   -- foldl (flip FAbs) (foldl1 (flip FFunc) ss) [0..i-1]

bkFFunc :: Sort -> Maybe (Int, [Sort])
bkFFunc t    = (maximum (0 : as),) <$> bkFun t'
  where
    (as, t') = bkAbs t

bkAbs :: Sort -> ([Int], Sort)
bkAbs (FAbs i t) = (i:is, t') where (is, t') = bkAbs t
bkAbs t          = ([], t)

bkFun :: Sort -> Maybe [Sort]
bkFun z@(FFunc _ _)  = Just (go z)
  where
    go (FFunc t1 t2) = t1 : go t2
    go t             = [t]
bkFun _              = Nothing

isPolyInst :: Sort -> Sort -> Bool
isPolyInst s t = isPoly s && not (isPoly t)

isPoly :: Sort -> Bool
isPoly (FAbs {}) = True
isPoly _         = False


instance Hashable FTycon where
  hashWithSalt i (TC s _) = hashWithSalt i s

instance Loc FTycon where
  srcSpan (TC c _) = srcSpan c

instance Hashable Sort

newtype Sub = Sub [(Int, Sort)] deriving (Generic)

instance Fixpoint Sort where
  toFix = toFixSort



toFixSort :: Sort -> Doc
toFixSort (FVar i)     = text "@" <> parens (toFix i)
toFixSort FInt         = text "int"
toFixSort FReal        = text "real"
toFixSort FFrac        = text "frac"
toFixSort (FObj x)     = toFix x
toFixSort FNum         = text "num"
toFixSort t@(FAbs _ _) = toFixAbsApp t
toFixSort t@(FFunc _ _)= toFixAbsApp t
toFixSort (FTC c)      = toFix c
toFixSort t@(FApp _ _) = toFixFApp (unFApp t)

toFixAbsApp :: Sort -> Doc
toFixAbsApp t = text "func" <> parens (toFix n <> text ", " <> toFix ts)
  where
    Just (vs, ss, s) = functionSort t
    n                = length vs
    ts               = ss ++ [s]

toFixFApp            :: ListNE Sort -> Doc
toFixFApp [t]        = toFixSort t
toFixFApp [FTC c, t]
  | isListTC c       = brackets $ toFixSort t
toFixFApp ts         = parens $ intersperse (text "") (toFixSort <$> ts)

instance Fixpoint FTycon where
  toFix (TC s _)       = toFix (val s)

instance Fixpoint DataField where
  toFix (DField x t) = toFix x <+> text ":" <+> toFix t

instance Fixpoint DataCtor where
  toFix (DCtor x flds) = toFix x <+> braces (intersperse comma (toFix <$> flds))

instance Fixpoint DataDecl where
  toFix (DDecl tc n ctors) = vcat ([header] ++ body ++ [footer])
    where
      header               = {- text "data" <+> -} toFix tc <+> toFix n <+> text "= ["
      body                 = [nest 2 (text "|" <+> toFix ct) | ct <- ctors]
      footer               = text "]"

instance PPrint FTycon where
  pprintTidy _ = toFix

instance PPrint DataField where
  pprintTidy _ = toFix

instance PPrint DataCtor where
  pprintTidy _ = toFix

instance PPrint DataDecl where
  pprintTidy _ = toFix

-------------------------------------------------------------------------
-- | Exported Basic Sorts -----------------------------------------------
-------------------------------------------------------------------------

boolSort, intSort, realSort, strSort, funcSort :: Sort
boolSort = fTyconSort boolFTyCon
strSort  = fTyconSort strFTyCon
intSort  = fTyconSort intFTyCon
realSort = fTyconSort realFTyCon
funcSort = fTyconSort funcFTyCon

setSort :: Sort -> Sort
setSort    = FApp (FTC setFTyCon)

bitVecSort :: Sort
bitVecSort = FApp (FTC $ symbolFTycon' bitVecName) (FTC $ symbolFTycon' size32Name)

mapSort :: Sort -> Sort -> Sort
mapSort = FApp . FApp (FTC (symbolFTycon' mapConName))

symbolFTycon' :: Symbol -> FTycon
symbolFTycon' = symbolFTycon . dummyLoc

fTyconSort :: FTycon -> Sort
fTyconSort c
  | c == intFTyCon  = FInt
  | c == realFTyCon = FReal
  | c == numFTyCon  = FNum
  | otherwise       = FTC c

basicSorts :: [Sort]
basicSorts = [FInt, boolSort] -- , setSort, mapSort, bitVecSort]

------------------------------------------------------------------------
sortSubst                  :: M.HashMap Symbol Sort -> Sort -> Sort
------------------------------------------------------------------------
sortSubst θ t@(FObj x)    = fromMaybe t (M.lookup x θ)
sortSubst θ (FFunc t1 t2) = FFunc (sortSubst θ t1) (sortSubst θ t2)
sortSubst θ (FApp t1 t2)  = FApp  (sortSubst θ t1) (sortSubst θ t2)
sortSubst θ (FAbs i t)    = FAbs i (sortSubst θ t)
sortSubst _  t            = t


instance B.Binary FTycon
instance B.Binary TCInfo
instance B.Binary Sort
instance B.Binary DataField
instance B.Binary DataCtor
instance B.Binary DataDecl
instance B.Binary Sub

instance NFData FTycon where
  rnf (TC x i) = x `seq` i `seq` ()


instance NFData TCInfo
instance NFData Sort
instance NFData DataField
instance NFData DataCtor
instance NFData DataDecl
instance NFData Sub


instance Monoid Sort where
  mempty            = FObj "any"
  mappend t1 t2
    | t1 == mempty  = t2
    | t2 == mempty  = t1
    | t1 == t2      = t1
    | otherwise     = errorstar $ "mappend-sort: conflicting sorts t1 =" ++ show t1 ++ " t2 = " ++ show t2
