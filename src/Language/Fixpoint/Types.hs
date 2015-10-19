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

-- | This module contains the data types, operations and
--   serialization functions for representing Fixpoint's
--   implication (i.e. subtyping) and well-formedness
--   constraints in Haskell. The actual constraint
--   solving is done by the `fixpoint.native` which
--   is written in Ocaml.

module Language.Fixpoint.Types (

  -- * Top level serialization
    Fixpoint (..)
  , toFixpoint
  , writeFInfo
  , FInfo, SInfo, GInfo (..)

  -- * Rendering
  , showFix
  , traceFix
  , resultDoc

  -- * Symbols
  , Symbol
  , KVar (..)
  , anfPrefix, tempPrefix, vv, vv_, intKvar
  , symChars, isNonSymbol, nonSymbol
  , isNontrivialVV
  , symbolSafeText, symbolSafeString

  -- * Creating Symbols
  , dummySymbol
  , intSymbol
  , tempSymbol

  -- * Embedding to Fixpoint Types
  , Sort (..), FTycon, TCEmb
  , sortFTycon
  , intFTyCon, boolFTyCon, realFTyCon, numFTyCon  -- TODO: hide these

  , intSort, realSort, propSort, boolSort, strSort, funcSort
  , listFTyCon
  , isListTC
  , fTyconSymbol, symbolFTycon, fTyconSort
  , fApp, fAppTC
  , fObj

  -- * Expressions and Predicates
  , SymConst (..)
  , Constant (..)
  , Bop (..), Brel (..)
  , Expr (..), Pred (..)
  , eVar, elit
  , eProp
  , pAnd, pOr, pIte
  , isTautoPred

  -- * Generalizing Embedding with Typeclasses
  , Symbolic (..)
  , Expression (..)
  , Predicate (..)

  -- * Constraints
  , WfC (..)
  , SubC, subcId, sid, senv, slhs, srhs, subC, lhsCs, rhsCs, wfC
  , SimpC (..)
  , Tag
  , TaggedC, WrappedC (..), clhs, crhs

  -- * Accessing Constraints
  , envCs
  , addIds, sinfo

  -- * Solutions
  , Result (..)
  , FixResult (..)
  , FixSolution

  -- * Environments
  , SEnv, SESearch(..)
  , emptySEnv, toListSEnv, fromListSEnv
  , mapSEnvWithKey
  , insertSEnv, deleteSEnv, memberSEnv, lookupSEnv
  , intersectWithSEnv
  , filterSEnv
  , lookupSEnvWithDistance

  , IBindEnv, BindId, BindMap
  , emptyIBindEnv, insertsIBindEnv, deleteIBindEnv, elemsIBindEnv

  , BindEnv, beBinds
  , insertBindEnv, emptyBindEnv, lookupBindEnv, mapBindEnv, adjustBindEnv
  , bindEnvFromList, bindEnvToList
  , unionIBindEnv

  -- * Refinements
  , Refa (..), SortedReft (..), Reft(..), Reftable(..)
  , raConjuncts

  -- * Constructing Refinements
  , refa
  , reft                    -- "smart
  , trueSortedReft          -- trivial reft
  , trueRefa                -- trivial reft
  , trueReft                -- trivial reft
  , exprReft                -- singleton: v == e
  , notExprReft             -- singleton: v /= e
  , uexprReft               -- singleton: v ~~ e
  , symbolReft              -- singleton: v == x
  , usymbolReft             -- singleton: v ~~ x
  , propReft                -- singleton: Prop(v) <=> p
  , predReft                -- any pred : p
  , reftPred, reftBind
  , isFunctionSortedReft, functionSort
  , isNonTrivial
  , isSingletonReft
  , isEVar
  , isFalse
  , flattenRefas, conjuncts
  , shiftVV
  , mapPredReft

  -- * Substitutions
  , Subst (..)
  , Subable (..)
  , mkSubst
  , isEmptySubst
  -- , emptySubst
  -- , catSubst
  , substExcept
  , substfExcept
  , subst1Except
  , sortSubst
  , targetSubstSyms

  -- * Functions on @Result@
  , colorResult

  -- * Cut KVars
  , Kuts (..)
  , ksEmpty
  , ksUnion
  , ksMember

  -- * Qualifiers
  , Qualifier (..)

  -- * Located Values
  , Located (..)
  , LocSymbol, LocText
  , locAt, dummyLoc, dummyPos, dummyName, isDummy

  -- * Partitions
  , CPart (..)
  , MCInfo (..)
  , mcInfo

  -- * FInfo to SInfo format conversion
  , convertFormat
  ) where

import           Debug.Trace               (trace)

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)

import           Control.Arrow             (second)
import qualified Data.Foldable             as F
import           Data.Functor
import           Data.Hashable
import           Data.List                 (foldl', intersect, nub, sort, sortBy, reverse)
import           Data.Monoid               hiding ((<>))
import           Data.String
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           Data.Traversable
import           GHC.Conc                  (getNumProcessors)
import           Control.DeepSeq           -- (NFData (..))
import           Data.Maybe                (isJust, mapMaybe, listToMaybe, fromMaybe)
import           Text.Printf               (printf)
-- import           Text.Parsec.Pos           (newPos, SourcePos (..))
import           Language.Fixpoint.Config
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Names
import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ

import           Data.Array                hiding (indices)
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S


class Fixpoint a where
  toFix    :: a -> Doc

  simplify :: a -> a
  simplify =  id

showFix :: (Fixpoint a) => a -> String
showFix =  render . toFix

traceFix     ::  (Fixpoint a) => String -> a -> a
traceFix s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showFix x) x

type TCEmb a    = M.HashMap a FTycon

exprSymbols :: Expr -> [Symbol]
exprSymbols = go
  where
    go (EVar x)        = [x]
--     go (ELit x _)      = [val x]
    go (EApp f es)     = val f : concatMap go es
    go (ENeg e)        = go e
    go (EBin _ e1 e2)  = go e1 ++ go e2
    go (EIte p e1 e2)  = predSymbols p ++ go e1 ++ go e2
    go (ECst e _)      = go e
    go _               = []

predSymbols :: Pred -> [Symbol]
predSymbols = go
  where
    go (PAnd ps)          = concatMap go ps
    go (POr ps)           = concatMap go ps
    go (PNot p)           = go p
    go (PIff p1 p2)       = go p1 ++ go p2
    go (PImp p1 p2)       = go p1 ++ go p2
    go (PBexp e)          = exprSymbols e
    go (PAtom _ e1 e2)    = exprSymbols e1 ++ exprSymbols e2
    go (PKVar _ (Su su))  = {- CUTSOLVER k : -} syms (M.keys su) ++ syms (M.elems su)
    go (PAll xts p)       = (fst <$> xts) ++ go p
    go _                  = []

---------------------------------------------------------------
---------- (Kut) Sets of Kvars --------------------------------
---------------------------------------------------------------

newtype KVar = KV {kv :: Symbol }
               deriving (Eq, Ord, Data, Typeable, Generic, IsString)

intKvar :: Integer -> KVar
intKvar = KV . intSymbol "k_"

instance Show KVar where
  show (KV x) = "$" ++ show x

instance Hashable KVar

newtype Kuts = KS { ksVars :: S.HashSet KVar }
               deriving (Eq, Show, Generic)

instance Fixpoint Kuts where
  toFix (KS s) = vcat $ ((text "cut " <>) . toFix) <$> S.toList s

ksEmpty :: Kuts
ksEmpty = KS S.empty

ksUnion :: [KVar] -> Kuts -> Kuts
ksUnion kvs (KS s') = KS (S.union (S.fromList kvs) s')

ksMember :: KVar -> Kuts -> Bool
ksMember k (KS s) = S.member k s
---------------------------------------------------------------
---------- Converting Constraints to Fixpoint Input -----------
---------------------------------------------------------------

instance (Eq a, Hashable a, Fixpoint a) => Fixpoint (S.HashSet a) where
  toFix xs = brackets $ sep $ punctuate (text ";") (toFix <$> S.toList xs)
  simplify = S.fromList . map simplify . S.toList

instance Fixpoint a => Fixpoint (Maybe a) where
  toFix    = maybe (text "Nothing") ((text "Just" <+>) . toFix)
  simplify = fmap simplify

instance Fixpoint a => Fixpoint [a] where
  toFix xs = brackets $ sep $ punctuate (text ";") (fmap toFix xs)
  simplify = map simplify

instance (Fixpoint a, Fixpoint b) => Fixpoint (a,b) where
  toFix   (x,y)  = toFix x <+> text ":" <+> toFix y
  simplify (x,y) = (simplify x, simplify y)

instance (Fixpoint a, Fixpoint b, Fixpoint c) => Fixpoint (a,b,c) where
  toFix   (x,y,z)  = toFix x <+> text ":" <+> toFix y <+> text ":" <+> toFix  z
  simplify (x,y,z) = (simplify x, simplify y,simplify z)

instance Fixpoint Bool where
  toFix True  = text "True"
  toFix False = text "False"
  simplify z  = z


----------------------------------------------------------------------
------------------------ Type Constructors ---------------------------
----------------------------------------------------------------------

newtype FTycon = TC LocSymbol deriving (Eq, Ord, Show, Data, Typeable, Generic)

intFTyCon, boolFTyCon, realFTyCon, funcFTyCon, numFTyCon, strFTyCon, propFTyCon, listFTyCon :: FTycon
intFTyCon  = TC $ dummyLoc "int"
boolFTyCon = TC $ dummyLoc "bool"
realFTyCon = TC $ dummyLoc "real"
numFTyCon  = TC $ dummyLoc "num"
funcFTyCon = TC $ dummyLoc "function"
strFTyCon  = TC $ dummyLoc strConName
propFTyCon = TC $ dummyLoc propConName
listFTyCon = TC $ dummyLoc listConName

isListTC :: FTycon -> Bool
isListTC (TC (Loc _ _ c)) = c == listConName || c == "List"
--isTupTC  (TC (Loc _ _ c)) = c == tupConName

fTyconSymbol :: FTycon -> Located Symbol
fTyconSymbol (TC s) = s

symbolFTycon :: LocSymbol -> FTycon
symbolFTycon c
  | val c == listConName
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

-- toFixArg             :: Sort -> Doc
-- toFixArg t@(FApp {}) = parens $ toFixSort t
-- toFixArg t           =          toFixSort t

--    fp s@(FApp _) = parens $ toFixSort s
--     fp s                = toFixSort s

-- toFixFApp :: FTycon -> [Sort] -> Doc
-- toFixFApp c [t]
--   | isListTC c            = brackets $ toFixSort t
-- toFixFApp c ts            = toFix c <+> intersperse space (fp <$> ts)
--   where
--     fp s@(FApp _ (_:_)) = parens $ toFixSort s
--     fp s                = toFixSort s

instance Fixpoint FTycon where
  toFix (TC s)       = toFix s

------------------------------------------------------------------------
sortSubst                  :: M.HashMap Symbol Sort -> Sort -> Sort
------------------------------------------------------------------------
sortSubst θ t@(FObj x)   = fromMaybe t (M.lookup x θ)
sortSubst θ (FFunc n ts) = FFunc n (sortSubst θ <$> ts)
sortSubst θ (FApp t1 t2) = FApp (sortSubst θ t1) (sortSubst θ t2)
sortSubst _  t           = t


instance Show Subst where
  show = showFix

instance Fixpoint Subst where
  toFix (Su m) = case hashMapToAscList m of
                   []  -> empty
                   xys -> hcat $ map (\(x,y) -> brackets $ toFix x <> text ":=" <> toFix y) xys

targetSubstSyms :: Subst -> [Symbol]
targetSubstSyms (Su ms) = syms $ M.elems ms


---------------------------------------------------------------
------------------------- Expressions -------------------------
---------------------------------------------------------------

-- | Uninterpreted constants that are embedded as  "constant symbol : Str"

data SymConst = SL !Text
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

data Constant = I !Integer
              | R !Double
              | L !Text !Sort
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

data Brel = Eq | Ne | Gt | Ge | Lt | Le | Ueq | Une
            deriving (Eq, Ord, Show, Data, Typeable, Generic)

data Bop  = Plus | Minus | Times | Div | Mod
            deriving (Eq, Ord, Show, Data, Typeable, Generic)
              -- NOTE: For "Mod" 2nd expr should be a constant or a var *)

data Expr = ESym !SymConst
          | ECon !Constant
          | EVar !Symbol
--           | ELit !LocSymbol !Sort
          | EApp !LocSymbol ![Expr]
          | ENeg !Expr
          | EBin !Bop !Expr !Expr
          | EIte !Pred !Expr !Expr
          | ECst !Expr !Sort
          | EBot
          deriving (Eq, Show, Data, Typeable, Generic)

elit :: Located Symbol -> Sort -> Expr
elit l s = ECon $ L (symbolText $ val l) s

instance Fixpoint Integer where
  toFix = integer

instance Fixpoint Double where
  toFix = double

instance Fixpoint Constant where
  toFix (I i)   = toFix i
  toFix (R i)   = toFix i
  toFix (L s t) = parens $ text "lit" <+> text "\"" <> toFix s <> text "\"" <+> toFix t

instance Fixpoint SymConst where
  toFix  = toFix . encodeSymConst

instance Fixpoint Symbol where
  toFix = toFix . symbolSafeText

instance Fixpoint KVar where
  toFix (KV k) = text "$" <> toFix k

instance Fixpoint Text where
  toFix = text . T.unpack


instance Fixpoint Brel where
  toFix Eq  = text "="
  toFix Ne  = text "!="
  toFix Ueq = text "~~"
  toFix Une = text "!~"
  toFix Gt  = text ">"
  toFix Ge  = text ">="
  toFix Lt  = text "<"
  toFix Le  = text "<="

instance Fixpoint Bop where
  toFix Plus  = text "+"
  toFix Minus = text "-"
  toFix Times = text "*"
  toFix Div   = text "/"
  toFix Mod   = text "mod"

instance Fixpoint Expr where
  toFix (ESym c)       = toFix $ encodeSymConst c
  toFix (ECon c)       = toFix c
  toFix (EVar s)       = toFix s
--   toFix (ELit s _)     = toFix s
  toFix (EApp f es)    = toFix f <> parens (toFix es)
  toFix (ENeg e)       = parens $ text "-"  <+> parens (toFix e)
  toFix (EBin o e1 e2) = parens $ toFix e1  <+> toFix o <+> toFix e2
  toFix (EIte p e1 e2) = parens $ text "if" <+> toFix p <+> text "then" <+> toFix e1 <+> text "else" <+> toFix e2
  toFix (ECst e so)    = parens $ toFix e   <+> text " : " <+> toFix so
  toFix (EBot)         = text "_|_"

----------------------------------------------------------
--------------------- Predicates -------------------------
----------------------------------------------------------


data Pred = PTrue
          | PFalse
          | PAnd   !(ListNE Pred)
          | POr    ![Pred]
          | PNot   !Pred
          | PImp   !Pred !Pred
          | PIff   !Pred !Pred
          | PBexp  !Expr
          | PAtom  !Brel  !Expr !Expr
          | PKVar  !KVar !Subst
          | PAll   ![(Symbol, Sort)] !Pred
          | PExist ![(Symbol, Sort)] !Pred
          | PTop
          deriving (Eq, Show, Data, Typeable, Generic)

{-@ PAnd :: ListNE Pred -> Pred @-}

instance Hashable Brel
instance Hashable Bop
instance Hashable SymConst
instance Hashable Constant

instance Fixpoint Pred where
  toFix PTop             = text "???"
  toFix PTrue            = text "true"
  toFix PFalse           = text "false"
  toFix (PBexp e)        = parens $ text "?" <+> toFix e
  toFix (PNot p)         = parens $ text "~" <+> parens (toFix p)
  toFix (PImp p1 p2)     = parens $ toFix p1 <+> text "=>" <+> toFix p2
  toFix (PIff p1 p2)     = parens $ toFix p1 <+> text "<=>" <+> toFix p2
  toFix (PAnd ps)        = text "&&" <+> toFix ps
  toFix (POr  ps)        = text "||" <+> toFix ps
  toFix (PAtom r e1 e2)  = parens $ toFix e1 <+> toFix r <+> toFix e2
  toFix (PKVar k su)     = toFix k <> toFix su
  toFix (PAll xts p)     = text "forall" <+> toFix xts <+> text "." <+> toFix p
  toFix (PExist xts p)   = text "exists" <+> toFix xts <+> text "." <+> toFix p

  simplify (PAnd [])     = PTrue
  simplify (POr  [])     = PFalse
  simplify (PAnd [p])    = simplify p
  simplify (POr  [p])    = simplify p

  simplify (PAnd ps)
    | any isContraPred ps = PFalse
    | otherwise           = PAnd $ filter (not . isTautoPred) $ map simplify ps

  simplify (POr  ps)
    | any isTautoPred ps = PTrue
    | otherwise          = POr  $ filter (not . isContraPred) $ map simplify ps

  simplify p
    | isContraPred p     = PFalse
    | isTautoPred  p     = PTrue
    | otherwise          = p

isContraPred   :: Pred -> Bool
isContraPred z = eqC z || (z `elem` contras)
  where
    contras    = [PFalse]

    eqC (PAtom Eq (ECon x) (ECon y))
               = x /= y
    eqC (PAtom Ueq (ECon x) (ECon y))
               = x /= y
    eqC (PAtom Ne x y)
               = x == y
    eqC (PAtom Une x y)
               = x == y
    eqC _      = False

isTautoPred   :: Pred -> Bool
isTautoPred z  = z == PTop || z == PTrue || eqT z
  where
    eqT (PAtom Le x y)
               = x == y
    eqT (PAtom Ge x y)
               = x == y
    eqT (PAtom Eq x y)
               = x == y
    eqT (PAtom Ueq x y)
               = x == y
    eqT (PAtom Ne (ECon x) (ECon y))
               = x /= y
    eqT (PAtom Une (ECon x) (ECon y))
               = x /= y
    eqT _      = False

isEVar :: Expr -> Bool
isEVar (EVar _) = True
isEVar _        = False

isEq  :: Brel -> Bool
isEq r          = r == Eq || r == Ueq


isSingletonReft :: Reft -> Maybe Expr
isSingletonReft (Reft (v, ra)) = firstMaybe (isSingletonExpr v) $ raConjuncts ra

raConjuncts  :: Refa -> [Pred]
raConjuncts  = conjuncts . raPred

firstMaybe :: (a -> Maybe b) -> [a] -> Maybe b
firstMaybe f = listToMaybe . mapMaybe f

--   where
--     go (PAtom r e1 e2) | e1 == EVar v && isEq r = Just e2
--                        | e2 == EVar v && isEq r = Just e1
--     go _                                        = Nothing

isSingletonExpr :: Symbol -> Pred -> Maybe Expr
isSingletonExpr v (PAtom r e1 e2)
  | e1 == EVar v && isEq r = Just e2
  | e2 == EVar v && isEq r = Just e1
isSingletonExpr _ _        = Nothing

pAnd          = simplify . PAnd
pOr           = simplify . POr
pIte p1 p2 p3 = pAnd [p1 `PImp` p2, (PNot p1) `PImp` p3]

mkProp        = PBexp . EApp (dummyLoc propConName) . (: [])

pprReft (Reft (v, Refa p)) d
  | isTautoPred p
  = d
  | otherwise
  = braces (toFix v <+> colon <+> d <+> text "|" <+> ppRas [Refa p])

pprReftPred (Reft (_, Refa p))
  | isTautoPred p
  = text "true"
  | otherwise
  = ppRas [Refa p]

ppRas = cat . punctuate comma . map toFix . flattenRefas

------------------------------------------------------------------------
-- | Generalizing Symbol, Expression, Predicate into Classes -----------
------------------------------------------------------------------------

-- | Values that can be viewed as Constants

-- | Values that can be viewed as Expressions

class Expression a where
  expr   :: a -> Expr

-- | Values that can be viewed as Predicates

class Predicate a where
  prop   :: a -> Pred

instance Expression Expr where
  expr = id

-- | The symbol may be an encoding of a SymConst.

instance Expression Symbol where
  expr s = maybe (eVar s) ESym (decodeSymConst s)
  -- expr = eVar

instance Expression Text where
  expr = ESym . SL

instance Expression Integer where
  expr = ECon . I

instance Expression Int where
  expr = expr . toInteger

instance Predicate Symbol where
  prop = eProp

instance Predicate Pred where
  prop = id

instance Predicate Bool where
  prop True  = PTrue
  prop False = PFalse

eVar ::  Symbolic a => a -> Expr
eVar = EVar . symbol

eProp ::  Symbolic a => a -> Pred
eProp = mkProp . eVar

relReft :: (Expression a) => Brel -> a -> Reft
relReft r e   = Reft (vv_, Refa $ PAtom r (eVar vv_)  (expr e))

exprReft, notExprReft, uexprReft ::  (Expression a) => a -> Reft
exprReft      = relReft Eq
notExprReft   = relReft Ne
uexprReft     = relReft Ueq

propReft      ::  (Predicate a) => a -> Reft
propReft p    = Reft (vv_, Refa $ PIff (eProp vv_) (prop p))

predReft      :: (Predicate a) => a -> Reft
predReft p    = Reft (vv_, Refa $ prop p)

reft :: Symbol -> Pred -> Reft
reft v p = Reft (v, Refa p)

mapPredReft :: (Pred -> Pred) -> Reft -> Reft
mapPredReft f (Reft (v, Refa p)) = Reft (v, Refa (f p))


---------------------------------------------------------------
----------------- Refinements ---------------------------------
---------------------------------------------------------------

newtype Refa = Refa { raPred :: Pred }
               deriving (Eq, Show, Data, Typeable, Generic)

newtype Reft = Reft (Symbol, Refa)
               deriving (Eq, Data, Typeable, Generic)

instance Show Reft where
  show (Reft x) = render $ toFix x

data SortedReft = RR { sr_sort :: !Sort, sr_reft :: !Reft }
                  deriving (Eq, Show, Data, Typeable, Generic)

isFunctionSortedReft :: SortedReft -> Bool
isFunctionSortedReft = isJust . functionSort . sr_sort

functionSort :: Sort -> Maybe (Int, [Sort], Sort)
functionSort (FFunc n ts) = Just (n, its, t)
  where
    (its, t)              = safeUnsnoc "functionSort" ts
functionSort _            = Nothing




isNonTrivial :: Reftable r => r -> Bool
isNonTrivial = not . isTauto

-- sortedReftValueVariable (RR _ (Reft (v,_))) = v

reftPred :: Reft -> Pred
reftPred (Reft (_, Refa p)) = p

reftBind :: Reft -> Symbol
reftBind (Reft (x, _)) = x

refa :: [Pred] -> Refa
refa = Refa . pAnd


---------------------------------------------------------------
-- | Environments ---------------------------------------------
---------------------------------------------------------------

-- unionSEnv :: SEnv a -> SEnv a -> SEnv a
-- unionSEnv (SE e1) (SE e2) = SE (M.union e1 e2)

toListSEnv              ::  SEnv a -> [(Symbol, a)]
toListSEnv (SE env)     = M.toList env

fromListSEnv            ::  [(Symbol, a)] -> SEnv a
fromListSEnv            = SE . M.fromList

mapSEnv f (SE env)      = SE (fmap f env)
mapSEnvWithKey f        = fromListSEnv . fmap f . toListSEnv
deleteSEnv x (SE env)   = SE (M.delete x env)
insertSEnv x y (SE env) = SE (M.insert x y env)
lookupSEnv x (SE env)   = M.lookup x env
emptySEnv               = SE M.empty
memberSEnv x (SE env)   = M.member x env
intersectWithSEnv f (SE m1) (SE m2) = SE (M.intersectionWith f m1 m2)
filterSEnv f (SE m)     = SE (M.filter f m)
lookupSEnvWithDistance x (SE env)
  = case M.lookup x env of
     Just z  -> Found z
     Nothing -> Alts $ symbol . T.pack <$> alts
  where
    alts       = takeMin $ zip (editDistance x' <$> ss) ss
    ss         = T.unpack . symbolText <$> fst <$> M.toList env
    x'         = T.unpack $ symbolText x
    takeMin xs = [z | (d, z) <- xs, d == getMin xs]
    getMin     = minimum . (fst <$>)

data SESearch a = Found a | Alts [Symbol]

-- | Functions for Indexed Bind Environment

emptyIBindEnv :: IBindEnv
emptyIBindEnv = FB S.empty

deleteIBindEnv :: BindId -> IBindEnv -> IBindEnv
deleteIBindEnv i (FB s) = FB (S.delete i s)

insertsIBindEnv :: [BindId] -> IBindEnv -> IBindEnv
insertsIBindEnv is (FB s) = FB (foldr S.insert s is)

elemsIBindEnv :: IBindEnv -> [BindId]
elemsIBindEnv (FB s) = S.toList s


-- | Functions for Global Binder Environment
insertBindEnv :: Symbol -> SortedReft -> BindEnv -> (BindId, BindEnv)
insertBindEnv x r (BE n m) = (n, BE (n + 1) (M.insert n (x, r) m))

emptyBindEnv :: BindEnv
emptyBindEnv = BE 0 M.empty

bindEnvFromList :: [(BindId, Symbol, SortedReft)] -> BindEnv
bindEnvFromList [] = emptyBindEnv
bindEnvFromList bs = BE (1 + maxId) be
  where
    maxId          = maximum $ fst3 <$> bs
    be             = M.fromList [(n, (x, r)) | (n, x, r) <- bs]

bindEnvToList :: BindEnv -> [(BindId, Symbol, SortedReft)]
bindEnvToList (BE _ be) = [(n, x, r) | (n, (x, r)) <- M.toList be]

mapBindEnv :: ((Symbol, SortedReft) -> (Symbol, SortedReft)) -> BindEnv -> BindEnv
mapBindEnv f (BE n m) = BE n $ M.map f m

lookupBindEnv :: BindId -> BindEnv -> (Symbol, SortedReft)
lookupBindEnv k (BE _ m) = fromMaybe err (M.lookup k m)
  where
    err                  = errorstar $ "lookupBindEnv: cannot find binder" ++ show k

unionIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
unionIBindEnv (FB m1) (FB m2) = FB $ m1 `S.union` m2

adjustBindEnv :: ((Symbol, SortedReft) -> (Symbol, SortedReft)) -> BindId -> BindEnv -> BindEnv
adjustBindEnv f i (BE n m) = BE n $ M.adjust f i m

instance Functor SEnv where
  fmap = mapSEnv

instance Fixpoint Refa where
  toFix (Refa p)     = toFix $ conjuncts p
  -- toFix (RPvar p)    = toFix p

instance Fixpoint Reft where
  toFix = pprReftPred

instance Fixpoint SortedReft where
  toFix (RR so (Reft (v, ra)))
    = braces
    $ toFix v <+> text ":" <+> toFix so <+> text "|" <+> toFix ra

instance Fixpoint BindEnv where
  toFix (BE _ m) = vcat $ map toFixBind $ hashMapToAscList m

toFixBind (i, (x, r)) = text "bind" <+> toFix i <+> toFix x <+> text ":" <+> toFix r

hashMapToAscList :: Ord a => M.HashMap a b -> [(a, b)]
hashMapToAscList = sortBy (\x y -> compare (fst x) (fst y)) . M.toList

-- instance (Fixpoint a) => Fixpoint (SEnv a) where
--   toFix (SE e)    = vcat $ map pprxt $ hashMapToAscList e
--     where
--       pprxt (x,t) = toFix x <+> colon <> colon  <+> toFix t

instance (Fixpoint a) => Fixpoint (SEnv a) where
   toFix (SE m)   = toFix (hashMapToAscList m)

instance Fixpoint (SEnv a) => Show (SEnv a) where
  show = render . toFix

-----------------------------------------------------------------------------
------------------- Constraints ---------------------------------------------
-----------------------------------------------------------------------------

{-@ type Tag = { v : [Int] | len(v) = 1 } @-}
type Tag           = [Int]

type BindId        = Int
type BindMap a     = M.HashMap BindId a -- (Symbol, SortedReft)

newtype IBindEnv   = FB (S.HashSet BindId) deriving (Eq, Data, Typeable, Generic)

newtype SEnv a     = SE { seBinds :: M.HashMap Symbol a }
                     deriving (Eq, Data, Typeable, Generic, F.Foldable, Traversable)

data SizedEnv a    = BE { beSize  :: Int
                        , beBinds :: BindMap a
                        } deriving (Eq, Show, Functor, F.Foldable, Generic, Traversable)

type BindEnv       = SizedEnv (Symbol, SortedReft)
-- Invariant: All BindIds in the map are less than beSize

data SubC a = SubC { _senv  :: !IBindEnv
                   , slhs  :: !SortedReft
                   , srhs  :: !SortedReft
                   , _sid   :: !(Maybe Integer)
                   , _stag  :: !Tag
                   , _sinfo :: !a
                   }
              deriving (Eq, Generic, Functor)

data SimpC a = SimpC { _cenv  :: !IBindEnv
                     , _crhs  :: !Pred
                     , _cid   :: !(Maybe Integer)
                     , _ctag  :: !Tag
                     , _cinfo :: !a
                     }
              deriving (Generic, Functor)

class TaggedC c a where
  senv  :: c a -> IBindEnv
  sid   :: c a -> Maybe Integer
  stag  :: c a -> Tag
  sinfo :: c a -> a
  clhs  :: BindEnv -> c a -> [(Symbol, SortedReft)]
  crhs  :: c a -> Pred

instance TaggedC SimpC a where
  senv      = _cenv
  sid       = _cid
  stag      = _ctag
  sinfo     = _cinfo
  crhs      = _crhs
  clhs be c = envCs be (senv c)

instance TaggedC SubC a where
  senv      = _senv
  sid       = _sid
  stag      = _stag
  sinfo     = _sinfo
  crhs      = reftPred . sr_reft . srhs
  clhs be c = sortedReftBind (slhs c) : envCs be (senv c)

sortedReftBind :: SortedReft -> (Symbol, SortedReft)
sortedReftBind sr = (x, sr)
  where
    Reft (x, _)   = sr_reft sr

-- lhsCs, rhsCs :: SubC a -> Reft
-- lhsCs      = sr_reft . slhs
-- rhsCs      = sr_reft . srhs

data WrappedC a where
  WrapC :: (TaggedC c a, Show (c a)) => { _x :: c a } -> WrappedC a

instance Show (WrappedC a) where
  show (WrapC x) = show x

instance TaggedC WrappedC a where
  senv  (WrapC x)   = senv  x
  sid   (WrapC x)   = sid   x
  stag  (WrapC x)   = stag  x
  sinfo (WrapC x)   = sinfo x
  crhs  (WrapC x)   = crhs  x
  clhs  b (WrapC x) = clhs b x

data WfC a  = WfC  { wenv  :: !IBindEnv
                   , wrft  :: !SortedReft
                   , wid   :: !(Maybe Integer)
                   , winfo :: !a
                   }
              deriving (Eq, Generic, Functor)

subcId :: (TaggedC c a) => c a -> Integer
subcId = mfromJust "subCId" . sid

---------------------------------------------------------------------------
-- | The output of the Solver
---------------------------------------------------------------------------
data Result a = Result { resStatus   :: FixResult (WrappedC a)
                       , resSolution :: M.HashMap KVar Pred }
                deriving (Generic, Show)
---------------------------------------------------------------------------

instance Monoid (Result a) where
  mempty        = Result mempty mempty
  mappend r1 r2 = Result stat soln
    where
      stat      = mappend (resStatus r1)   (resStatus r2)
      soln      = mappend (resSolution r1) (resSolution r2)

-- instance Functor Result where
--   fmap f (Result x y) = Result (fmap (fmap f) x) y

data FixResult a = Crash [a] String
                 | Safe
                 | Unsafe ![a]
                 | UnknownError !String
                   deriving (Show, Generic)

type FixSolution = M.HashMap KVar Pred

instance Eq a => Eq (FixResult a) where
  Crash xs _ == Crash ys _        = xs == ys
  Unsafe xs == Unsafe ys          = xs == ys
  Safe      == Safe               = True
  _         == _                  = False

instance Monoid (FixResult a) where
  mempty                          = Safe
  mappend Safe x                  = x
  mappend x Safe                  = x
  mappend _ c@(Crash _ _)         = c
  mappend c@(Crash _ _) _         = c
  mappend (Unsafe xs) (Unsafe ys) = Unsafe (xs ++ ys)
  mappend u@(UnknownError _) _    = u
  mappend _ u@(UnknownError _)    = u

instance Functor FixResult where
  fmap f (Crash xs msg)   = Crash (f <$> xs) msg
  fmap f (Unsafe xs)      = Unsafe (f <$> xs)
  fmap _ Safe             = Safe
  fmap _ (UnknownError d) = UnknownError d

instance (Ord a, Fixpoint a) => Fixpoint (FixResult (SubC a)) where
  toFix Safe             = text "Safe"
  toFix (UnknownError d) = text $ "Unknown Error: " ++ d
  toFix (Crash xs msg)   = vcat $ [ text "Crash!" ] ++  pprSinfos "CRASH: " xs ++ [parens (text msg)]
  toFix (Unsafe xs)      = vcat $ text "Unsafe:" : pprSinfos "WARNING: " xs

pprSinfos :: (Ord a, Fixpoint a) => String -> [SubC a] -> [Doc]
pprSinfos msg = map ((text msg <>) . toFix) . sort . fmap sinfo


resultDoc :: (Ord a, Fixpoint a) => FixResult a -> Doc
resultDoc Safe             = text "Safe"
resultDoc (UnknownError d) = text $ "Unknown Error: " ++ d
resultDoc (Crash xs msg)   = vcat $ text ("Crash!: " ++ msg) : (((text "CRASH:" <+>) . toFix) <$> xs)
resultDoc (Unsafe xs)      = vcat $ text "Unsafe:"           : (((text "WARNING:" <+>) . toFix) <$> xs)

colorResult :: FixResult a -> Moods
colorResult (Safe)      = Happy
colorResult (Unsafe _)  = Angry
colorResult (_)         = Sad

instance Fixpoint a => Show (WfC a) where
  show = showFix

instance Fixpoint a => Show (SubC a) where
  show = showFix

instance Fixpoint a => Show (SimpC a) where
  show = showFix

instance Fixpoint (IBindEnv) where
  toFix (FB ids) = text "env" <+> toFix ids

instance Fixpoint a => Fixpoint (SubC a) where
  toFix c     = hang (text "\n\nconstraint:") 2 bd
     where bd =   -- text "env" <+> toFix (senv c)
                  toFix (senv c)
              $+$ text "lhs" <+> toFix (slhs c)
              $+$ text "rhs" <+> toFix (srhs c)
              $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "constraint" <+> pprId (sid c)) (toFix (sinfo c))

instance Fixpoint a => Fixpoint (SimpC a) where
  toFix c     = hang (text "\n\nsimpleConstraint:") 2 bd
     where bd =   -- text "env" <+> toFix (senv c)
                  toFix (senv c)
              $+$ text "rhs" <+> toFix (crhs c)
              $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "simpleConstraint" <+> pprId (sid c)) (toFix (sinfo c))


instance Fixpoint a => Fixpoint (WfC a) where
  toFix w     = hang (text "\n\nwf:") 2 bd
    where bd  =   -- text "env"  <+> toFix (wenv w)
                  toFix (wenv w)
              $+$ text "reft" <+> toFix (wrft w)
              $+$ pprId (wid w)
              $+$ toFixMeta (text "wf" <+> pprId (wid w)) (toFix (winfo w))

toFixMeta :: Doc -> Doc -> Doc
toFixMeta k v = text "// META" <+> k <+> text ":" <+> v
             --  $+$ text "\n"

pprId (Just i)  = text "id" <+> tshow i
pprId _         = text ""

instance Fixpoint Int where
  toFix = tshow

-------------------------------------------------------
------------------- Substitutions ---------------------
-------------------------------------------------------

class Subable a where
  syms   :: a -> [Symbol]
  substa :: (Symbol -> Symbol) -> a -> a
  -- substa f  = substf (EVar . f)

  substf :: (Symbol -> Expr) -> a -> a
  subst  :: Subst -> a -> a
  subst1 :: a -> (Symbol, Expr) -> a
  subst1 y (x, e) = subst (Su $ M.fromList [(x,e)]) y

subst1Except :: (Subable a) => [Symbol] -> a -> (Symbol, Expr) -> a
subst1Except xs z su@(x, _)
  | x `elem` xs = z
  | otherwise   = subst1 z su

substfExcept :: (Symbol -> Expr) -> [Symbol] -> Symbol -> Expr
substfExcept f xs y = if y `elem` xs then EVar y else f y

substExcept  :: Subst -> [Symbol] -> Subst
-- substExcept  (Su m) xs = Su (foldr M.delete m xs)
substExcept (Su xes) xs = Su $ M.filterWithKey (const . not . (`elem` xs)) xes

instance Subable Symbol where
  substa f                 = f
  substf f x               = subSymbol (Just (f x)) x
  subst su x               = subSymbol (Just $ appSubst su x) x -- subSymbol (M.lookup x s) x
  syms x                   = [x]

subSymbol (Just (EVar y)) _ = y
subSymbol Nothing         x = x
subSymbol a               b = errorstar (printf "Cannot substitute symbol %s with expression %s" (showFix b) (showFix a))

instance Subable Expr where
  syms                     = exprSymbols
  substa f                 = substf (EVar . f)
  substf f (EApp s es)     = EApp (substf f s) $ map (substf f) es
  substf f (ENeg e)        = ENeg (substf f e)
  substf f (EBin op e1 e2) = EBin op (substf f e1) (substf f e2)
  substf f (EIte p e1 e2)  = EIte (substf f p) (substf f e1) (substf f e2)
  substf f (ECst e so)     = ECst (substf f e) so
  substf f (EVar x)        = f x
  substf _ e               = e

  subst su (EApp f es)     = EApp (subst su f) $ map (subst su) es
  subst su (ENeg e)        = ENeg (subst su e)
  subst su (EBin op e1 e2) = EBin op (subst su e1) (subst su e2)
  subst su (EIte p e1 e2)  = EIte (subst su p) (subst su e1) (subst su e2)
  subst su (ECst e so)     = ECst (subst su e) so
  subst su (EVar x)        = appSubst su x
  subst _ e                = e


instance Subable Pred where
  syms                     = predSymbols
  substa f                 = substf (EVar . f)
  substf f (PAnd ps)       = PAnd $ map (substf f) ps
  substf f (POr  ps)       = POr  $ map (substf f) ps
  substf f (PNot p)        = PNot $ substf f p
  substf f (PImp p1 p2)    = PImp (substf f p1) (substf f p2)
  substf f (PIff p1 p2)    = PIff (substf f p1) (substf f p2)
  substf f (PBexp e)       = PBexp $ substf f e
  substf f (PAtom r e1 e2) = PAtom r (substf f e1) (substf f e2)
  substf _ p@(PKVar _ _)   = p
  substf _  (PAll _ _)     = errorstar "substf: FORALL"
  substf _  p              = p

  subst su (PAnd ps)       = PAnd $ map (subst su) ps
  subst su (POr  ps)       = POr  $ map (subst su) ps
  subst su (PNot p)        = PNot $ subst su p
  subst su (PImp p1 p2)    = PImp (subst su p1) (subst su p2)
  subst su (PIff p1 p2)    = PIff (subst su p1) (subst su p2)
  subst su (PBexp e)       = PBexp $ subst su e
  subst su (PAtom r e1 e2) = PAtom r (subst su e1) (subst su e2)
  subst su (PKVar k su')   = PKVar k $ su' `catSubst` su
  subst _  (PAll _ _)      = errorstar "subst: FORALL"
  subst su (PExist bs p)   = PExist bs $ subst (substExcept su (fst <$> bs)) p
  subst _  p               = p

instance Subable Refa where
  syms (Refa p)           = syms p
  -- syms (RKvar k (Su su'))  = k : concatMap syms ({- M.elems -} su')
  subst su (Refa p)       = Refa $ subst su p
  substa f                 = substf (EVar . f)
  substf f (Refa p)       = Refa (substf f p)

instance (Subable a, Subable b) => Subable (a,b) where
  syms  (x, y)   = syms x ++ syms y
  subst su (x,y) = (subst su x, subst su y)
  substf f (x,y) = (substf f x, substf f y)
  substa f (x,y) = (substa f x, substa f y)

instance Subable a => Subable [a] where
  syms   = concatMap syms
  subst  = map . subst
  substf = map . substf
  substa = map . substa

instance Subable a => Subable (M.HashMap k a) where
  syms   = syms . M.elems
  subst  = M.map . subst
  substf = M.map . substf
  substa = M.map . substa

instance Subable Reft where
  syms (Reft (v, ras))      = v : syms ras
  substa f (Reft (v, ras))  = Reft (f v, substa f ras)
  subst su (Reft (v, ras))  = Reft (v, subst (substExcept su [v]) ras)
  substf f (Reft (v, ras))  = Reft (v, substf (substfExcept f [v]) ras)
  subst1 (Reft (v, ras)) su = Reft (v, subst1Except [v] ras su)


instance Subable SortedReft where
  syms               = syms . sr_reft
  subst su (RR so r) = RR so $ subst su r
  substf f (RR so r) = RR so $ substf f r
  substa f (RR so r) = RR so $ substa f r

newtype Subst = Su (M.HashMap Symbol Expr)
                deriving (Eq, Data, Typeable, Generic)

appSubst :: Subst -> Symbol -> Expr
appSubst (Su s) x = fromMaybe (EVar x) (M.lookup x s)

emptySubst :: Subst
emptySubst = Su M.empty

catSubst :: Subst -> Subst -> Subst
catSubst = unsafeCatSubst

mkSubst :: [(Symbol, Expr)] -> Subst
mkSubst = unsafeMkSubst . M.fromList . reverse

isEmptySubst :: Subst -> Bool
isEmptySubst (Su xes) = M.null xes

unsafeMkSubst  = Su

unsafeCatSubst (Su s1) θ2@(Su s2) = Su $ M.union s1' s2
  where
    s1'                           = subst θ2 <$> s1

-- TODO: this is **not used**, because of degenerate substitutions.
-- e.g. consider: s1 = [v := v], s2 = [v := x].
-- We want s1 `cat` s2 to be [v := x] and not [v := v] ...

--unsafeCatSubstIgnoringDead (Su s1) (Su s2) = Su $ s1' ++ s2'
--  where
--    s1' = second (subst (Su s2')) <$> s1
--    s2' = filter (\(x,_) -> (x `notElem` (fst <$> s1))) s2

-- TODO: nano-js throws all sorts of issues, will look into this later...
-- but also, the check is too conservative, because of degenerate substitutions,
-- see above.
--safeCatSubst θ1@(Su s1) θ2@(Su s2)
--  | null $ intersect xs1 xs2
--  = unsafeCatSubst θ1 θ2
--  | otherwise
--  = errorstar msg
--  where
--    s1' = second (subst (Su s2)) <$> s1
--    xs1 = fst <$> s1
--    xs2 = fst <$> s2
--    msg = printf "Fixpoint.Types catSubst on overlapping substitutions θ1 = %s, θ2 = %s" (showFix θ1) (showFix θ2)


--safeMkSubst θ
--  | nub θ == θ
--  = Su θ
--  | otherwise
--  = errorstar msg
--  where
--    msg = printf "Fixpoint.Types mkSubst on overlapping substitution θ = %s" (showFix θ)

instance Monoid Subst where
  mempty  = emptySubst
  mappend = catSubst

------------------------------------------------------------
------------- Generally Useful Refinements -----------------
------------------------------------------------------------

symbolReft    :: (Symbolic a) => a -> Reft
symbolReft    = exprReft . eVar

usymbolReft   :: (Symbolic a) => a -> Reft
usymbolReft   = uexprReft . eVar

vv_ :: Symbol
vv_ = vv Nothing

trueSortedReft :: Sort -> SortedReft
trueSortedReft = (`RR` trueReft)

trueReft, falseReft :: Reft
trueReft  = Reft (vv_, trueRefa)
falseReft = Reft (vv_, Refa PFalse)

trueRefa  :: Refa
trueRefa  = Refa PTrue

flattenRefas ::  [Refa] -> [Refa]
flattenRefas         = concatMap flatRa
  where
    flatRa (Refa p)  = Refa <$> flatP p
    flatP  (PAnd ps) = concatMap flatP ps
    flatP  p         = [p]

--squishRefas     :: [Refa] -> [Refa]
--squishRefas ras =  [squish (raPred <$> ras)]
--  where
--    squish      = Refa . pAnd . sortNub . filter (not . isTautoPred) . concatMap conjuncts

conjuncts :: Pred -> [Pred]
conjuncts (PAnd ps) = concatMap conjuncts ps
conjuncts p
  | isTautoPred p   = []
  | otherwise       = [p]

----------------------------------------------------------------
-- | Serialization ---------------------------------------------
----------------------------------------------------------------

instance B.Binary SourcePos where
  put = B.put . ofSourcePos
  get = toSourcePos <$> B.get

instance B.Binary KVar

instance (Hashable a, Eq a, B.Binary a) => B.Binary (S.HashSet a) where
  put = B.put . S.toList
  get = S.fromList <$> B.get

instance (Hashable k, Eq k, B.Binary k, B.Binary v) => B.Binary (M.HashMap k v) where
  put = B.put . M.toList
  get = M.fromList <$> B.get

instance B.Binary Kuts
instance B.Binary Qualifier
instance B.Binary FTycon
instance B.Binary Sort
instance B.Binary Sub
instance B.Binary Subst
instance B.Binary IBindEnv
instance B.Binary BindEnv
instance B.Binary Constant
instance B.Binary SymConst
instance B.Binary Brel
instance B.Binary Bop
instance B.Binary Expr
instance B.Binary Pred
instance B.Binary Refa
instance B.Binary Reft
instance B.Binary SortedReft
instance (B.Binary a) => B.Binary (SEnv a)
instance (B.Binary a) => B.Binary (FixResult a)
instance (B.Binary a) => B.Binary (SubC a)
instance (B.Binary a) => B.Binary (WfC a)
instance (B.Binary a) => B.Binary (SimpC a)
instance (B.Binary (c a), B.Binary a) => B.Binary (GInfo c a)
instance (B.Binary a) => B.Binary (Located a)

----------------------------------------------------------------
-- | Strictness ------------------------------------------------
----------------------------------------------------------------

instance NFData SourcePos where
  rnf = rnf . ofSourcePos

ofSourcePos :: SourcePos -> (SourceName, Line, Column)
ofSourcePos p = (f, l, c)
  where
   f = sourceName   p
   l = sourceLine   p
   c = sourceColumn p

toSourcePos :: (SourceName, Line, Column) -> SourcePos
toSourcePos (f, l, c) = newPos f l c

instance NFData KVar
instance NFData Kuts
instance NFData Qualifier
instance NFData FTycon
instance NFData Sort
instance NFData Sub
instance NFData Subst
instance NFData IBindEnv
instance NFData BindEnv
instance NFData Constant
instance NFData SymConst
instance NFData Brel
instance NFData Bop
instance NFData Expr
instance NFData Pred
instance NFData Refa
instance NFData Reft
instance NFData SortedReft
instance (NFData a) => NFData (SEnv a)
instance (NFData a) => NFData (FixResult a)
instance (NFData a) => NFData (SubC a)
instance (NFData a) => NFData (WfC a)
instance (NFData a) => NFData (SimpC a)
instance (NFData (c a), NFData a) => NFData (GInfo c a)
instance (NFData a) => NFData (Located a)

-- instance NFData Kuts where
--   rnf (KS s) = rnf s

-- instance NFData Qualifier where
--   rnf (Q x1 x2 x3 _) = rnf x1 `seq` rnf x2 `seq` rnf x3

-- instance NFData FTycon where
--   rnf (TC c)       = rnf c
--
-- instance NFData Sort where
  -- rnf (FVar x)     = rnf x
  -- rnf (FFunc n ts) = rnf n `seq` (rnf <$> ts) `seq` ()
  -- rnf (FApp t1 t2) = rnf t1 `seq` rnf t2 `seq` ()
  -- rnf (z)          = z `seq` ()
--
-- instance NFData Sub where
--  rnf (Sub x) = rnf x

-- instance NFData Subst where
--  rnf (Su x) = rnf x

-- instance NFData IBindEnv where
--  rnf (FB x) = rnf x

-- instance NFData BindEnv where
--  rnf (BE x m) = rnf x `seq` rnf m

-- instance NFData Constant where
  -- rnf (I x)     = rnf x
  -- rnf (R x)     = rnf x
  -- rnf (L s t) = rnf s `seq` rnf t

-- instance NFData SymConst where
--  rnf (SL x) = rnf x



-- instance NFData Expr where
  -- rnf (ESym x)        = rnf x
  -- rnf (ECon x)        = rnf x
  -- rnf (EVar x)        = rnf x
-- --   rnf (ELit x1 x2)    = rnf x1 `seq` rnf x2
  -- rnf (EApp x1 x2)    = rnf x1 `seq` rnf x2
  -- rnf (ENeg x1)       = rnf x1
  -- rnf (EBin x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  -- rnf (EIte x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  -- rnf (ECst x1 x2)    = rnf x1 `seq` rnf x2
  -- rnf (_)             = ()
--
-- instance NFData Pred where
  -- rnf (PAnd x)         = rnf x
  -- rnf (POr  x)         = rnf x
  -- rnf (PNot x)         = rnf x
  -- rnf (PBexp x)        = rnf x
  -- rnf (PImp x1 x2)     = rnf x1 `seq` rnf x2
  -- rnf (PIff x1 x2)     = rnf x1 `seq` rnf x2
  -- rnf (PAll x1 x2)     = rnf x1 `seq` rnf x2
  -- rnf (PAtom x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  -- rnf (_)              = ()
--
-- instance NFData Refa where
  -- rnf (Refa x)     = rnf x
--
-- instance NFData Reft where
  -- rnf (Reft (v, ras)) = rnf v `seq` rnf ras

-- instance NFData SortedReft where
--  rnf (RR so r) = rnf so `seq` rnf r

-- instance (NFData a) => NFData (SubC a) where
  -- rnf (SubC x1 x2 x3 x4 x5 x6)
    -- = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6
--
-- instance (NFData a) => NFData (WfC a) where
  -- rnf (WfC x1 x2 x3 x4)
    -- = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4

-- instance (NFData a) => NFData (Located a) where
  -- FIXME: no instance NFData SrcSpan
  -- rnf (Loc _ _  x) = rnf x

----------------------------------------------------------------------------
-------------- Hashable Instances -----------------------------------------
---------------------------------------------------------------------------

instance Hashable FTycon where
  hashWithSalt i (TC s) = hashWithSalt i s

---------------------------------------------------------------------------
-------- Constraint Constructor Wrappers ----------------------------------
---------------------------------------------------------------------------

wfC  :: IBindEnv -> SortedReft -> Maybe Integer -> a -> WfC a
wfC  = WfC

subC :: IBindEnv -> SortedReft -> SortedReft -> Maybe Integer -> Tag -> a -> [SubC a]
subC γ sr1 sr2 i y z = [SubC γ sr1' (sr2' r2') i y z | r2' <- reftConjuncts r2]
   where
     RR t1 r1          = sr1
     RR t2 r2          = sr2
     sr1'              = RR t1 $ shiftVV r1  vv'
     sr2' r2'          = RR t2 $ shiftVV r2' vv'
     vv'               = mkVV i

reftConjuncts :: Reft -> [Reft]
reftConjuncts (Reft (v, ra)) = [Reft (v, ra') | ra' <- refaConjuncts ra]

refaConjuncts :: Refa -> [Refa]
refaConjuncts (Refa p)       = [Refa p' | p' <- conjuncts p, not $ isTautoPred p']

mkVV :: Maybe Integer -> Symbol
mkVV (Just i)  = vv $ Just i
mkVV Nothing   = vvCon

lhsCs, rhsCs :: SubC a -> Reft
lhsCs      = sr_reft . slhs
rhsCs      = sr_reft . srhs

envCs :: BindEnv -> IBindEnv -> [(Symbol, SortedReft)]
envCs be env = [lookupBindEnv i be | i <- elemsIBindEnv env]


--removeLhsKvars cs vs
--  = error "TODO:cutsolver: removeLhsKvars (why is this function needed?)"

-- CUTSOLVER   = cs {slhs = goRR (slhs cs)}
-- CUTSOLVER  where goRR rr                     = rr{sr_reft = goReft (sr_reft rr)}
-- CUTSOLVER        goReft (Reft(v, rs))        = Reft(v, filter f rs)
-- CUTSOLVER        f (RKvar v _) | v `elem` vs = False
-- CUTSOLVER        f r                         = True

--trueSubCKvar k = subC emptyIBindEnv mempty rhs  Nothing [0]
--  where
--    rhs        = RR mempty (Reft (vv_, Refa $ PKVar k mempty))

shiftVV :: Reft -> Symbol -> Reft
shiftVV r@(Reft (v, ras)) v'
   | v == v'   = r
   | otherwise = Reft (v', subst1 ras (v, EVar v'))


addIds = zipWith (\i c -> (i, shiftId i $ c {_sid = Just i})) [1..]
  where -- Adding shiftId to have distinct VV for SMT conversion
    shiftId i c = c { slhs = shiftSR i $ slhs c }
                    { srhs = shiftSR i $ srhs c }
    shiftSR i sr = sr { sr_reft = shiftR i $ sr_reft sr }
    shiftR i r@(Reft (v, _)) = shiftVV r (v `mappend` symbol (show i))


------------------------------------------------------------------------
----------------- Qualifiers -------------------------------------------
------------------------------------------------------------------------


data Qualifier = Q { q_name   :: Symbol           -- ^ Name
                   , q_params :: [(Symbol, Sort)] -- ^ Parameters
                   , q_body   :: Pred             -- ^ Predicate
                   , q_pos    :: !SourcePos          -- ^ Source Location
                   }
               deriving (Eq, Show, Data, Typeable, Generic)

{-
instance Show Qualifier where
  show = render . toFix
-}

instance Fixpoint Qualifier where
  toFix = pprQual

instance Fixpoint () where
  toFix _ = text "()"

pprQual (Q n xts p l) = text "qualif" <+> text (symbolString n) <> parens args <> colon <+> toFix p <+> text "//" <+> toFix l
  where
    args              = intersperse comma (toFix <$> xts)

------------------------------------------------------------------------
----------------- Top-Level Constraint System --------------------------
------------------------------------------------------------------------

type FInfo a   = GInfo SubC a
type SInfo a   = GInfo SimpC a
data GInfo c a =
  FI { cm       :: M.HashMap Integer (c a)
     , ws       :: ![WfC a]
     , bs       :: !BindEnv
     , lits     :: !(SEnv Sort)
     , kuts     :: Kuts
     , quals    :: ![Qualifier]
     , bindInfo :: M.HashMap BindId a
     , fileName :: FilePath
     }
  deriving (Eq, Show, Functor, Generic)

instance Monoid Kuts where
  mempty        = KS S.empty
  mappend k1 k2 = KS $ S.union (ksVars k1) (ksVars k2)

instance Monoid (SEnv a) where
  mempty        = SE M.empty
  mappend s1 s2 = SE $ M.union (seBinds s1) (seBinds s2)

instance Monoid BindEnv where
  mempty = BE 0 M.empty
  mappend (BE 0 _) b = b
  mappend b (BE 0 _) = b
  mappend _ _        = errorstar "mappend on non-trivial BindEnvs"

instance Monoid (GInfo c a) where
  mempty        = FI M.empty mempty mempty mempty mempty mempty mempty mempty
  mappend i1 i2 = FI { cm       = mappend (cm i1)       (cm i2)
                     , ws       = mappend (ws i1)       (ws i2)
                     , bs       = mappend (bs i1)       (bs i2)
                     , lits     = mappend (lits i1)     (lits i2)
                     , kuts     = mappend (kuts i1)     (kuts i2)
                     , quals    = mappend (quals i1)    (quals i2)
                     , bindInfo = mappend (bindInfo i1) (bindInfo i2)
                     , fileName = fileName i1
                     }

($++$) :: Doc -> Doc -> Doc
x $++$ y = x $+$ text "\n" $+$ y

toFixpoint :: (Fixpoint a, Fixpoint (c a)) => Config -> GInfo c a -> Doc
toFixpoint cfg x' =    qualsDoc x'
                  $++$ kutsDoc  x'
                  $++$ conDoc   x'
                  $++$ bindsDoc x'
                  $++$ csDoc    x'
                  $++$ wsDoc    x'
                  $++$ binfoDoc x'
                  $++$ text "\n"
  where
    conDoc        = vcat     . map toFixConstant . toListSEnv . lits
    csDoc         = vcat     . map toFix . M.elems . cm
    wsDoc         = vcat     . map toFix . ws
    kutsDoc       = toFix    . kuts
    bindsDoc      = toFix    . bs
    qualsDoc      = vcat     . map toFix . quals
    metaDoc (i,d) = toFixMeta (text "bind" <+> toFix i) (toFix d)
    mdata         = metadata cfg
    binfoDoc
      | mdata     = vcat     . map metaDoc . M.toList . bindInfo
      | otherwise = \_ -> text "\n"

toFixConstant (c, so)
  = text "constant" <+> toFix c <+> text ":" <+> parens (toFix so)

writeFInfo :: (Fixpoint a, Fixpoint (c a)) => Config -> GInfo c a -> FilePath -> IO ()
writeFInfo cfg fi f = writeFile f (render $ toFixpoint cfg fi)

-------------------------------------------------------------------------
-- | A Class Predicates for Valid Refinements Types ---------------------
-------------------------------------------------------------------------

class (Monoid r, Subable r) => Reftable r where
  isTauto :: r -> Bool
  ppTy    :: r -> Doc -> Doc

  top     :: r -> r
  top _   =  mempty

  bot     :: r -> r

  meet    :: r -> r -> r
  meet    = mappend

  toReft  :: r -> Reft
  ofReft  :: Reft -> r
  params  :: r -> [Symbol]          -- ^ parameters for Reft, vv + others

instance Monoid Pred where
  mempty      = PTrue
  mappend p q = pAnd [p, q]
  mconcat     = pAnd

instance Monoid Refa where
  mempty          = Refa mempty
  mappend ra1 ra2 = Refa $ mappend (raPred ra1) (raPred ra2)

instance Monoid Reft where
  mempty  = trueReft
  mappend = meetReft

meetReft (Reft (v, ra)) (Reft (v', ra'))
  | v == v'          = Reft (v , ra  `mappend` ra')
  | v == dummySymbol = Reft (v', ra' `mappend` (ra `subst1`  (v , EVar v')))
  | otherwise        = Reft (v , ra  `mappend` (ra' `subst1` (v', EVar v )))

instance Subable () where
  syms _      = []
  subst _ ()  = ()
  substf _ () = ()
  substa _ () = ()

instance Reftable () where
  isTauto _ = True
  ppTy _  d = d
  top  _    = ()
  bot  _    = ()
  meet _ _  = ()
  toReft _  = mempty
  ofReft _  = mempty
  params _  = []

instance Reftable Reft where
  isTauto  = all isTautoPred . conjuncts . reftPred
  ppTy     = pprReft
  toReft   = id
  ofReft   = id
  params _ = []

  bot    _        = falseReft
  top (Reft(v,_)) = Reft (v, mempty)

instance Monoid Sort where
  mempty            = FObj "any"
  mappend t1 t2
    | t1 == mempty  = t2
    | t2 == mempty  = t1
    | t1 == t2      = t1
    | otherwise     = errorstar $ "mappend-sort: conflicting sorts t1 =" ++ show t1 ++ " t2 = " ++ show t2

instance Monoid SortedReft where
  mempty        = RR mempty mempty
  mappend t1 t2 = RR (mappend (sr_sort t1) (sr_sort t2)) (mappend (sr_reft t1) (sr_reft t2))

instance Reftable SortedReft where
  isTauto  = isTauto . toReft
  ppTy     = ppTy . toReft
  toReft   = sr_reft
  ofReft   = error "No instance of ofReft for SortedReft"
  params _ = []
  bot s    = s { sr_reft = falseReft }

class Falseable a where
  isFalse :: a -> Bool

instance Falseable Pred where
  isFalse (PFalse) = True
  isFalse _        = False

instance Falseable Refa where
  isFalse (Refa p) = isFalse p

instance Falseable Reft where
  isFalse (Reft (_, ra)) = isFalse $ raPred ra

---------------------------------------------------------------
-- | String Constants -----------------------------------------
---------------------------------------------------------------

--symConstLits    :: (SymConsts (c a)) => GInfo c a -> [(Symbol, Sort)]
--symConstLits fi = [(encodeSymConst c, sortSymConst c) | c <- symConsts fi]

-- | Replace all symbol-representations-of-string-literals with string-literal
--   Used to transform parsed output from fixpoint back into fq.


instance Symbolic SymConst where
  symbol = encodeSymConst

encodeSymConst        :: SymConst -> Symbol
encodeSymConst (SL s) = litPrefix `mappend` symbol s

sortSymConst          :: SymConst -> Sort
sortSymConst (SL _)   = strSort

decodeSymConst :: Symbol -> Maybe SymConst
decodeSymConst = fmap (SL . symbolText) . stripPrefix litPrefix

-- class SymConsts a where
  -- symConsts :: a -> [SymConst]
--
-- instance (SymConsts (c a)) => SymConsts (GInfo c a) where
  -- symConsts fi = sortNub $ csLits ++ bsLits ++ qsLits
    -- where
      -- csLits   = concatMap symConsts                   $ M.elems  $  cm    fi
      -- bsLits   = concatMap (symConsts . snd) $ M.elems $ beBinds $  bs    fi
      -- qsLits   = concatMap symConsts $                   q_body  <$> quals fi
--
-- instance SymConsts (SubC a) where
  -- symConsts c  = symConsts (slhs c) ++
                 -- symConsts (srhs c)
--
-- instance SymConsts (SimpC a) where
  -- symConsts c  = symConsts (crhs c)
--
-- instance SymConsts SortedReft where
  -- symConsts = symConsts . sr_reft
--
-- instance SymConsts Reft where
  -- symConsts (Reft (_, ra)) = symConsts ra
--
-- instance SymConsts Refa where
  -- symConsts (Refa p)           = symConsts p
--
-- instance SymConsts Expr where
  -- symConsts (ESym c)       = [c]
  -- symConsts (EApp _ es)    = concatMap symConsts es
  -- symConsts (ENeg e)       = symConsts e
  -- symConsts (EBin _ e e')  = concatMap symConsts [e, e']
  -- symConsts (EIte p e e')  = symConsts p ++ concatMap symConsts [e, e']
  -- symConsts (ECst e _)     = symConsts e
  -- symConsts _              = []
--
-- instance SymConsts Pred where
  -- symConsts (PNot p)           = symConsts p
  -- symConsts (PAnd ps)          = concatMap symConsts ps
  -- symConsts (POr ps)           = concatMap symConsts ps
  -- symConsts (PImp p q)         = concatMap symConsts [p, q]
  -- symConsts (PIff p q)         = concatMap symConsts [p, q]
  -- symConsts (PAll _ p)         = symConsts p
  -- symConsts (PBexp e)          = symConsts e
  -- symConsts (PAtom _ e e')     = concatMap symConsts [e, e']
  -- symConsts (PKVar _ (Su xes)) = concatMap symConsts $ M.elems xes
  -- symConsts _                  = []
--

---------------------------------------------------------------
-- | Edit Distance --------------------------------------------
---------------------------------------------------------------


editDistance :: Eq a => [a] -> [a] -> Int
editDistance xs ys = table ! (m,n)
    where
    (m,n) = (length xs, length ys)
    x     = array (1,m) (zip [1..] xs)
    y     = array (1,n) (zip [1..] ys)

    table :: Array (Int,Int) Int
    table = array bnds [(ij, dist ij) | ij <- range bnds]
    bnds  = ((0,0),(m,n))

    dist (0,j) = j
    dist (i,0) = i
    dist (i,j) = minimum [table ! (i-1,j) + 1, table ! (i,j-1) + 1,
        if x ! i == y ! j then table ! (i-1,j-1) else 1 + table ! (i-1,j-1)]


-----------------------------------------------------------------------------
-- | Located Values ---------------------------------------------------------
-----------------------------------------------------------------------------

data Located a = Loc { loc  :: !SourcePos -- ^ Start Position
                     , locE :: !SourcePos -- ^ End Position
                     , val  :: a
                     } deriving (Data, Typeable, Generic)

instance (IsString a) => IsString (Located a) where
  fromString = dummyLoc . fromString

type LocSymbol = Located Symbol
type LocText   = Located Text


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

isDummy :: (Symbolic a) => a -> Bool
isDummy a = symbol a == symbol dummyName

instance Fixpoint SourcePos where
  toFix = text . show

instance Fixpoint a => Fixpoint (Located a) where
  toFix = toFix . val

instance Symbolic a => Symbolic (Located a) where
  symbol = symbol . val

instance Expression a => Expression (Located a) where
  expr   = expr . val

instance Functor Located where
  fmap f (Loc l l' x) =  Loc l l' (f x)


instance F.Foldable Located where
  foldMap f (Loc _ _ x) = f x

instance Traversable Located where
  traverse f (Loc l l' x) = Loc l l' <$> f x

instance Show a => Show (Located a) where
  show (Loc l l' x) = show x ++ " defined from: " ++ show l ++ " to: " ++ show l'

instance Eq a => Eq (Located a) where
  (Loc _ _ x) == (Loc _ _ y) = x == y

instance Ord a => Ord (Located a) where
  compare x y = compare (val x) (val y)

instance Subable a => Subable (Located a) where
  syms (Loc _ _ x)   = syms x
  substa f (Loc l l' x) = Loc l l' (substa f x)
  substf f (Loc l l' x) = Loc l l' (substf f x)
  subst su (Loc l l' x) = Loc l l' (subst su x)

instance Hashable a => Hashable (Located a) where
  hashWithSalt i = hashWithSalt i . val


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

-------------------------------------------------------------------------
-- | Constraint Partition Container -------------------------------------
-------------------------------------------------------------------------


data CPart a = CPart { pws :: [WfC a]
                     , pcm :: M.HashMap Integer (SubC a)
                     , cFileName :: FilePath
                     }

instance Monoid (CPart a) where
   mempty = CPart mempty mempty mempty
   mappend l r = CPart { pws = pws l `mappend` pws r
                       , pcm = pcm l `mappend` pcm r
                       , cFileName = cFileName l
                       }

-------------------------------------------------------------------------
-- | Multicore info -----------------------------------------------------
-------------------------------------------------------------------------

data MCInfo = MCInfo { mcCores :: Int
                     , mcMinPartSize :: Int
                     , mcMaxPartSize :: Int
                     } deriving (Show)

mcInfo :: Config -> IO MCInfo
mcInfo c = do
   np <- getNumProcessors
   let nc = fromMaybe np (cores c)
   return MCInfo { mcCores = nc
                 , mcMinPartSize = minPartSize c
                 , mcMaxPartSize = maxPartSize c
                 }

---------------------------------------------------------------------------
-- | FInfo to SInfo conversion
---------------------------------------------------------------------------
convertFormat :: (Fixpoint a) => FInfo a -> SInfo a
---------------------------------------------------------------------------
convertFormat fi = fi' { cm = subcToSimpc <$> cm fi' }
  where
    fi'          = foldl' blowOutVV fi is
    is           = M.keys $ cm fi

subcToSimpc :: SubC a -> SimpC a
subcToSimpc s = SimpC
  { _cenv     = senv s
  , _crhs     = reftPred $ sr_reft $ srhs s
  , _cid      = sid s
  , _ctag     = stag s
  , _cinfo    = sinfo s
  }

blowOutVV :: FInfo a -> Integer -> FInfo a
blowOutVV fi scId = fi { bs = be', cm = cm' }
  where
    subc          = cm fi M.! scId
    sr            = slhs subc
    x             = reftBind $ sr_reft sr
    (bindId, be') = insertBindEnv x sr $ bs fi
    subc'         = subc { _senv = insertsIBindEnv [bindId] $ senv subc }
    cm'           = M.insert scId subc' $ cm fi
