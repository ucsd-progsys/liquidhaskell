{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}

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
  , FInfo (..)

  -- * Rendering
  , showFix
  , traceFix
  , resultDoc

  -- * Symbols
  , Symbol
  , KVar
  , anfPrefix, tempPrefix, vv, vv_, intKvar
  , symChars, isNonSymbol, nonSymbol
  , isNontrivialVV
  , symbolText, symbolString

  -- * Creating Symbols
  , dummySymbol
  , intSymbol
  , tempSymbol
  , qualifySymbol
  , suffixSymbol

  -- * Embedding to Fixpoint Types
  , Sort (..), FTycon, TCEmb
  , intFTyCon
  , boolFTyCon
  , realFTyCon
  , strFTyCon
  , propFTyCon
  , appFTyCon
  , fTyconSymbol
  , symbolFTycon

  , strSort
  , fApp
  , fObj
  , isListTC
  , isFAppTyTC

  -- * Expressions and Predicates
  , SymConst (..)
  , Constant (..)
  , Bop (..), Brel (..)
  , Expr (..), Pred (..)
  , eVar
  , eProp
  , pAnd, pOr, pIte
  , isTautoPred
  , symConstLits

  -- * Generalizing Embedding with Typeclasses
  , Symbolic (..)
  , Expression (..)
  , Predicate (..)

  -- * Constraints and Solutions
  , SubC
  , WfC (..)
  , sid, sgrd, senv, slhs, subC, lhsCs, rhsCs, wfC
  , envCs
  , Tag
  , FixResult (..)
  , FixSolution
  , addIds, sinfo
  , trueSubCKvar
  , removeLhsKvars


  -- * Environments
  , SEnv, SESearch(..)
  , emptySEnv, toListSEnv, fromListSEnv
  -- , mapSEnv
  , mapSEnvWithKey
  , insertSEnv, deleteSEnv, memberSEnv, lookupSEnv
  , intersectWithSEnv
  , filterSEnv
  , lookupSEnvWithDistance

  , FEnv, insertFEnv
  , IBindEnv, BindId, BindMap
  , emptyIBindEnv, insertsIBindEnv, deleteIBindEnv, elemsIBindEnv

  , BindEnv
  , insertBindEnv, emptyBindEnv, lookupBindEnv, mapBindEnv
  , bindEnvFromList, bindEnvToList
  , unionIBindEnv

  -- * Refinements
  , Refa (..), SortedReft (..), Reft(..), Reftable(..)

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
  , isFunctionSortedReft
  , isNonTrivial
  , isSingletonReft
  , isEVar
  , isFalse
  , flattenRefas, squishRefas, conjuncts
  , shiftVV
  , mapPredReft
 
  -- * Substitutions
  , Subst
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

  -- * Qualifiers
  , Qualifier (..)

  -- * FQ Definitions
  , Def (..)

  -- * Located Values
  , Located (..)
  , LocSymbol, LocText
  , dummyLoc, dummyPos, dummyName, isDummy
  ) where

import           Debug.Trace               (trace)

import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)

import           Data.Char                 (toLower)
import qualified Data.Foldable             as F
import           Data.Functor
import           Data.Hashable
-- import           Data.Interned
import           Data.List                 (foldl', intersect, nub, sort)
import           Data.Monoid               hiding ((<>))
import           Data.String
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           Data.Traversable
import           Control.DeepSeq
import           Control.Exception         (assert)
import           Data.Maybe                (fromMaybe)
import           Text.Printf               (printf)

import           Language.Fixpoint.Misc
import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ

import           Data.Array                hiding (indices)
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import           Language.Fixpoint.Names


class Fixpoint a where
  toFix    :: a -> Doc

  simplify :: a -> a
  simplify =  id

------------------------------------------------------------------------
-- | Entities in Query File --------------------------------------------
------------------------------------------------------------------------

data Def a
  = Srt Sort
  | Axm Pred
  | Cst (SubC a)
  | Wfc (WfC a)
  | Con Symbol Sort
  | Qul Qualifier
  | Kut Symbol
  | IBind Int Symbol SortedReft
  deriving (Generic)
  --  Sol of solbind
  --  Dep of FixConstraint.dep

------------------------------------------------------------------------

showFix :: (Fixpoint a) => a -> String
showFix =  render . toFix

traceFix     ::  (Fixpoint a) => String -> a -> a
traceFix s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showFix x) x

type TCEmb a    = M.HashMap a FTycon

-- instance (Eq a, Hashable a) => Monoid (TCEmb a) where
--   mappend m1 m2 = M.fromList (M.toList m1 ++ M.toList m2)
--   mempty        = M.empty

exprSymbols :: Expr -> [Symbol]
exprSymbols = go
  where
    go (EVar x)        = [x]
    -- go (EDat x _)      = [x]
    go (ELit x _)      = [val x]
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
    go (PKVar k (Su su')) = k : concatMap syms su'
    go (PAll xts p)       = (fst <$> xts) ++ go p
    go _                  = []

---------------------------------------------------------------
---------- (Kut) Sets of Kvars --------------------------------
---------------------------------------------------------------
type KVar    = Symbol

newtype Kuts = KS (S.HashSet KVar) deriving (Show)

instance NFData Kuts where
  rnf (KS _) = () -- rnf s

instance Fixpoint Kuts where
  toFix (KS s) = vcat $ ((text "cut " <>) . toFix) <$> S.toList s

ksEmpty :: Kuts
ksEmpty             = KS S.empty

ksUnion :: [Symbol] -> Kuts -> Kuts
ksUnion kvs (KS s') = KS (S.union (S.fromList kvs) s')

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

toFixGs :: SEnv SortedReft -> Doc
toFixGs (SE e) = vcat  $ map (toFixConstant . mapSnd sr_sort) $ hashMapToAscList e

toFixConstant (c, so)
  = text "constant" <+> toFix c <+> text ":" <+> toFix so

----------------------------------------------------------------------
------------------------ Type Constructors ---------------------------
----------------------------------------------------------------------

newtype FTycon = TC LocSymbol deriving (Eq, Ord, Show, Data, Typeable, Generic)

intFTyCon, boolFTyCon, realFTyCon, strFTyCon, propFTyCon, appFTyCon :: FTycon
intFTyCon  = TC $ dummyLoc "int"
boolFTyCon = TC $ dummyLoc "bool"
realFTyCon = TC $ dummyLoc "real"
strFTyCon  = TC $ dummyLoc strConName
propFTyCon = TC $ dummyLoc propConName
appFTyCon  = TC $ dummyLoc "FAppTy"

isListTC, isFAppTyTC :: FTycon -> Bool
isListTC (TC (Loc _ _ c)) = c == listConName
isTupTC  (TC (Loc _ _ c)) = c == tupConName
isFAppTyTC = (== appFTyCon)

fTyconSymbol :: FTycon -> Located Symbol
fTyconSymbol (TC s) = s

symbolFTycon :: LocSymbol -> FTycon
symbolFTycon c
  | val c == listConName
  = TC $ fmap (const listConName) c
  | otherwise
  = TC c

-- stringSort   :: String -> Sort
-- stringSort s = FApp (stringFTycon s) []
--            -- ALTERNATIVEL = FObj . stringSymbol

fApp                  :: Either FTycon Sort -> [Sort] -> Sort
fApp (Left c) ts
  | c == intFTyCon    = FInt
  | c == realFTyCon   = FReal
  | otherwise         = fAppSorts (fTyconSort c) ts
fApp (Right t) ts     = fAppSorts t ts

fAppSorts :: Sort -> [Sort] -> Sort
fAppSorts = foldl' (\t1 t2 -> FApp appFTyCon [t1, t2])

fTyconSort :: FTycon -> Sort
fTyconSort = (`FApp` [])

fObj :: LocSymbol -> Sort
fObj = fTyconSort . TC


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
          | FApp FTycon [Sort]   -- ^ constructed type
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance Hashable Sort

newtype Sub = Sub [(Int, Sort)]

instance Fixpoint Sort where
  toFix = toFixSort

toFixSort :: Sort -> Doc
toFixSort (FVar i)        = text "@"   <> parens (toFix i)
toFixSort FInt            = text "int"
toFixSort FReal           = text "real"
toFixSort FFrac           = text "frac"
toFixSort (FObj x)        = toFix x
toFixSort FNum            = text "num"
toFixSort (FFunc n ts)    = text "func" <> parens (toFix n <> text ", " <> toFix ts)
toFixSort (FApp c [t])
  | isListTC c            = brackets $ toFixSort t
toFixSort (FApp c [FApp c' [],t])
  | isFAppTyTC c &&
    isListTC c'           = brackets $ toFixSort t
toFixSort (FApp c ts)     = toFix c <+> intersperse space (fp <$> ts)
    where
      fp s@(FApp _ (_:_)) = parens $ toFixSort s
      fp s                = toFixSort s


instance Fixpoint FTycon where
  toFix (TC s)       = toFix s


------------------------------------------------------------------------
sortSubst                  :: M.HashMap Symbol Sort -> Sort -> Sort
------------------------------------------------------------------------
sortSubst θ t@(FObj x)   = fromMaybe t (M.lookup x θ)
sortSubst θ (FFunc n ts) = FFunc n (sortSubst θ <$> ts)
sortSubst θ (FApp c ts)  = FApp c  (sortSubst θ <$> ts)
sortSubst _  t           = t


instance Show Subst where
  show = showFix

instance Fixpoint Subst where
  toFix (Su m) = case {- hashMapToAscList -} m of
                   []  -> empty
                   xys -> hcat $ map (\(x,y) -> brackets $ toFix x <> text ":=" <> toFix y) xys

targetSubstSyms :: Subst -> [Symbol]
targetSubstSyms (Su ms) = syms $ snd <$> ms


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
          | ELit !LocSymbol !Sort
          | EApp !LocSymbol ![Expr]
          | ENeg !Expr
          | EBin !Bop !Expr !Expr
          | EIte !Pred !Expr !Expr
          | ECst !Expr !Sort
          | EBot
          deriving (Eq, Ord, Show, Data, Typeable, Generic)

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
  toFix = text . encode . T.unpack . symbolText

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
  toFix (ELit s _)     = toFix s
  toFix (EApp f es)    = toFix f <> parens (toFix es)
  toFix (ENeg e)       = parens $ text "-" <+> parens (toFix e)
  toFix (EBin o e1 e2) = parens $ toFix e1 <+> toFix o <+> toFix e2
  toFix (EIte p e1 e2) = parens $ toFix p <+> text "?" <+> toFix e1 <+> text ":" <+> toFix e2
  toFix (ECst e so)    = parens $ toFix e <+> text " : " <+> toFix so
  toFix (EBot)         = text "_|_"

----------------------------------------------------------
--------------------- Predicates -------------------------
----------------------------------------------------------


data Pred = PTrue
          | PFalse
          | PAnd   ![Pred]
          | POr    ![Pred]
          | PNot   !Pred
          | PImp   !Pred !Pred
          | PIff   !Pred !Pred
          | PBexp  !Expr
          | PAtom  !Brel !Expr !Expr
          | PKVar  !KVar !Subst
          | PAll   ![(Symbol, Sort)] !Pred
          | PExist ![(Symbol, Sort)] !Pred
          | PTop
          deriving (Eq, Ord, Show, Data, Typeable, Generic)

{-@ type ListNE a = {v:[a] | 0 < len v} @-}

{-@ PAnd :: ListNE Pred -> Pred @-}



instance Hashable Brel
instance Hashable Bop
instance Hashable SymConst
instance Hashable Constant
instance Hashable Subst
instance Hashable Expr
instance Hashable Pred

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
  toFix (PExist xts p)   = text "exist"  <+> toFix xts <+> text "." <+> toFix p

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
isSingletonReft (Reft (v, Refa (PAtom r e1 e2)))
  | e1 == EVar v && isEq r = Just e2
  | e2 == EVar v && isEq r = Just e1
isSingletonReft _          = Nothing

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
               deriving (Eq, Ord, Show, Data, Typeable, Generic)

newtype Reft = Reft (Symbol, Refa)
               deriving (Eq, Ord, Data, Typeable, Generic)

instance Show Reft where
  show (Reft x) = render $ toFix x

data SortedReft = RR { sr_sort :: !Sort, sr_reft :: !Reft }
                  deriving (Eq, Show, Data, Typeable, Generic)

isFunctionSortedReft :: SortedReft -> Bool
isFunctionSortedReft (RR (FFunc _ _) _) = True
isFunctionSortedReft _                  = False

isNonTrivial :: Reftable r => r -> Bool
isNonTrivial = not .isTauto

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
bindEnvFromList bs = BE (1 + nbs) be'
  where
    nbs            = length bs
    be             = M.fromList [(n, (x, r)) | (n, x, r) <- bs]
    be'            = assert (M.size be == nbs) be

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

insertFEnv   = insertSEnv . lower
  where lower s = case unconsSym s of
                    Nothing     -> s
                    Just (c,s') -> consSym (toLower c) s'

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
type FEnv          = SEnv SortedReft
type BindMap a     = M.HashMap BindId a -- (Symbol, SortedReft)

newtype IBindEnv   = FB (S.HashSet BindId) deriving (Data, Typeable)
newtype SEnv a     = SE { seBinds :: M.HashMap Symbol a }
                     deriving (Eq, Data, Typeable, Generic, F.Foldable, Traversable)

data BindEnv       = BE { beSize  :: Int
                        , beBinds :: BindMap (Symbol, SortedReft)
                        }
                     deriving (Show)

data SubC a = SubC { senv  :: !IBindEnv
                   , sgrd  :: !Pred
                   , slhs  :: !SortedReft
                   , srhs  :: !SortedReft
                   , sid   :: !(Maybe Integer)
                   , stag  :: !Tag
                   , sinfo :: !a
                   }
              deriving (Generic)

data WfC a  = WfC  { wenv  :: !IBindEnv
                   , wrft  :: !SortedReft
                   , wid   :: !(Maybe Integer)
                   , winfo :: !a
                   }
              deriving (Generic)

data FixResult a = Crash [a] String
                 | Safe
                 | Unsafe ![a]
                 | UnknownError !String
                   deriving (Show, Generic)

type FixSolution = M.HashMap Symbol Pred

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


colorResult (Safe)      = Happy
colorResult (Unsafe _)  = Angry
colorResult (_)         = Sad

instance Show (WfC a) where
  show = showFix

instance Show (SubC a) where
  show = showFix

instance Fixpoint (IBindEnv) where
  toFix (FB ids) = text "env" <+> toFix ids

instance Fixpoint (SubC a) where
  toFix c     = hang (text "\n\nconstraint:") 2 bd
     where bd =   -- text "env" <+> toFix (senv c)
                  toFix (senv c)
              $+$ text "grd" <+> toFix (sgrd c)
              $+$ text "lhs" <+> toFix (slhs c)
              $+$ text "rhs" <+> toFix (srhs c)
              $+$ (pprId (sid c) <+> pprTag (stag c))

instance Fixpoint (WfC a) where
  toFix w     = hang (text "\n\nwf:") 2 bd
    where bd  =   -- text "env"  <+> toFix (wenv w)
                  toFix (wenv w)
              $+$ text "reft" <+> toFix (wrft w)
              $+$ pprId (wid w)

pprId (Just i)  = text "id" <+> tshow i
pprId _         = text ""

pprTag []       = text ""
pprTag is       = text "tag" <+> toFix is

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
  -- subst1 y (x, e) = subst (Su $ M.singleton x e) y
  subst1 y (x, e) = subst (Su [(x,e)]) y

subst1Except :: (Subable a) => [Symbol] -> a -> (Symbol, Expr) -> a
subst1Except xs z su@(x, _)
  | x `elem` xs = z
  | otherwise   = subst1 z su

substfExcept :: (Symbol -> Expr) -> [Symbol] -> Symbol -> Expr
substfExcept f xs y = if y `elem` xs then EVar y else f y

substExcept  :: Subst -> [Symbol] -> Subst
-- substExcept  (Su m) xs = Su (foldr M.delete m xs)
substExcept  (Su xes) xs = Su $ filter (not . (`elem` xs) . fst) xes

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
  substf f e@(EVar x)      = f x
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

newtype Subst = Su [(Symbol, Expr)]
                deriving (Eq, Ord, Data, Typeable, Generic)

appSubst :: Subst -> Symbol -> Expr
appSubst (Su s) x        = fromMaybe (EVar x) (lookup x s)

emptySubst :: Subst
emptySubst = Su [] -- M.empty

catSubst :: Subst -> Subst -> Subst
catSubst = unsafeCatSubst

mkSubst  :: [(Symbol, Expr)] -> Subst
mkSubst  = unsafeMkSubst

isEmptySubst :: Subst -> Bool
isEmptySubst (Su xes) = null xes

unsafeMkSubst  = Su

unsafeCatSubst (Su s1) θ2@(Su s2) = Su $ s1' ++ s2
  where
    s1'                           = mapSnd (subst θ2) <$> s1

-- TODO: this is **not used**, because of degenerate substitutions.
-- e.g. consider: s1 = [v := v], s2 = [v := x].
-- We want s1 `cat` s2 to be [v := x] and not [v := v] ...

unsafeCatSubstIgnoringDead (Su s1) (Su s2) = Su $ s1' ++ s2'
  where
    s1' = mapSnd (subst (Su s2')) <$> s1
    s2' = filter (\(x,_) -> (x `notElem` (fst <$> s1))) s2

-- TODO: nano-js throws all sorts of issues, will look into this later...
-- but also, the check is too conservative, because of degenerate substitutions,
-- see above.
safeCatSubst θ1@(Su s1) θ2@(Su s2)
  | null $ intersect xs1 xs2
  = unsafeCatSubst θ1 θ2
  | otherwise
  = errorstar msg
  where
    s1' = mapSnd (subst (Su s2)) <$> s1
    xs1 = fst <$> s1
    xs2 = fst <$> s2
    msg = printf "Fixpoint.Types catSubst on overlapping substitutions θ1 = %s, θ2 = %s" (showFix θ1) (showFix θ2)


safeMkSubst θ
  | nub θ == θ
  = Su θ
  | otherwise
  = errorstar msg
  where
    msg = printf "Fixpoint.Types mkSubst on overlapping substitution θ = %s" (showFix θ)

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

trueReft  = Reft (vv_, trueRefa)
falseReft = Reft (vv_, Refa PFalse)

trueRefa  :: Refa
trueRefa  = Refa PTrue

flattenRefas ::  [Refa] -> [Refa]
flattenRefas         = concatMap flatRa
  where
    flatRa (Refa p)  = Refa <$> flatP p
    flatRa ra        = [ra]
    flatP  (PAnd ps) = concatMap flatP ps
    flatP  p         = [p]

squishRefas     :: [Refa] -> [Refa]
squishRefas ras =  [squish (raPred <$> ras)]
  where
    squish      = Refa . pAnd . sortNub . filter (not . isTautoPred) . concatMap conjuncts

conjuncts (PAnd ps)          = concatMap conjuncts ps
conjuncts p | isTautoPred p  = []
            | otherwise      = [p]
----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance NFData FTycon where
  rnf (TC c)       = rnf c

instance NFData Sort where
  rnf (FVar x)     = rnf x
  rnf (FFunc n ts) = rnf n `seq` (rnf <$> ts) `seq` ()
  rnf (FApp c ts)  = rnf c `seq` (rnf <$> ts) `seq` ()
  rnf (z)          = z `seq` ()

instance NFData Sub where
  rnf (Sub x) = rnf x

instance NFData Subst where
  rnf (Su x) = rnf x

instance NFData FEnv where
  rnf (SE x) = rnf x

instance NFData IBindEnv where
  rnf (FB x) = rnf x

instance NFData BindEnv where
  rnf (BE x m) = rnf x `seq` rnf m

instance NFData Constant where
  rnf (I x)     = rnf x
  rnf (R x)     = rnf x
  rnf (L s t) = rnf s `seq` rnf t

instance NFData SymConst where
  rnf (SL x) = rnf x

instance NFData Brel
instance NFData Bop

instance NFData Expr where
  rnf (ESym x)        = rnf x
  rnf (ECon x)        = rnf x
  rnf (EVar x)        = rnf x
  -- rnf (EDat x1 x2)    = rnf x1 `seq` rnf x2
  rnf (ELit x1 x2)    = rnf x1 `seq` rnf x2
  rnf (EApp x1 x2)    = rnf x1 `seq` rnf x2
  rnf (ENeg x1)       = rnf x1
  rnf (EBin x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (EIte x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (ECst x1 x2)    = rnf x1 `seq` rnf x2
  rnf (_)             = ()

instance NFData Pred where
  rnf (PAnd x)         = rnf x
  rnf (POr  x)         = rnf x
  rnf (PNot x)         = rnf x
  rnf (PBexp x)        = rnf x
  rnf (PImp x1 x2)     = rnf x1 `seq` rnf x2
  rnf (PIff x1 x2)     = rnf x1 `seq` rnf x2
  rnf (PAll x1 x2)     = rnf x1 `seq` rnf x2
  rnf (PAtom x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (_)              = ()

instance NFData Refa where
  rnf (Refa x)     = rnf x
  -- rnf (RKvar x1 x2) = rnf x1 `seq` rnf x2
  -- rnf (RPvar _)     = () -- rnf x

instance NFData Reft where
  rnf (Reft (v, ras)) = rnf v `seq` rnf ras

instance NFData SortedReft where
  rnf (RR so r) = rnf so `seq` rnf r

instance (NFData a) => NFData (SubC a) where
  rnf (SubC x1 x2 x3 x4 x5 x6 x7)
    = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7

instance (NFData a) => NFData (WfC a) where
  rnf (WfC x1 x2 x3 x4)
    = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4

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

-- subC :: IBindEnv -> Pred -> SortedReft -> SortedReft -> Maybe Integer -> Tag -> a -> [SubC a]
-- subC γ p (RR t1 r1) (RR t2 (Reft (v2, ra2s))) i y z
--   = error "TODO:subC" -- NEW [subC' r2' | r2' <- [r2P], not $ isTauto r2']
--   where
--     subC' r2'  = SubC γ p (RR t1 (shiftVV r1 vv')) (RR t2 (shiftVV r2' vv')) i y z
--     r2P        = Reft (v2, ra2s) -- ORIG [ra | ra@(Refa _  ) <- ra2s])
--     -- ORIG r2K        = Reft (v2, [ra | ra@(RKvar _ _) <- ra2s])
--     vv'        = mkVV i


-- ORIG subC γ p (RR t1 r1) (RR t2 (Reft (v2, ra2s))) x y z
-- ORIG   = [subC' r2' | r2' <- [r2K, r2P], not $ isTauto r2']
-- ORIG   where
-- ORIG     subC' r2'  = SubC γ p (RR t1 (shiftVV r1 vvCon)) (RR t2 (shiftVV r2' vvCon)) x y z
-- ORIG     r2K        = Reft (v2, [ra | ra@(RKvar _ _) <- ra2s])
-- ORIG     r2P        = Reft (v2, [ra | ra@(RConc _  ) <- ra2s])


subC :: IBindEnv -> Pred -> SortedReft -> SortedReft -> Maybe Integer -> Tag -> a -> [SubC a]
-- subC γ p (RR t1 r1) (RR t2 r2) i y z
subC γ p sr1 sr2 i y z = [SubC γ p sr1' (sr2' r2') i y z | r2' <- reftConjuncts r2]
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

-- mkFEnv :: BindEnv -> IBindEnv -> FEnv
-- mkFEnv be env = fromListSEnv $ envCs be env



removeLhsKvars cs vs
  = error "TODO:cutsolver: removeLhsKvars (why is this function needed?)"

-- CUTSOLVER   = cs {slhs = goRR (slhs cs)}
-- CUTSOLVER  where goRR rr                     = rr{sr_reft = goReft (sr_reft rr)}
-- CUTSOLVER        goReft (Reft(v, rs))        = Reft(v, filter f rs)
-- CUTSOLVER        f (RKvar v _) | v `elem` vs = False
-- CUTSOLVER        f r                         = True

trueSubCKvar k = subC emptyIBindEnv PTrue mempty rhs  Nothing [0]
  where
    rhs        = RR mempty (Reft (vv_, Refa $ PKVar k mempty))

shiftVV :: Reft -> Symbol -> Reft
shiftVV r@(Reft (v, ras)) v'
   | v == v'   = r
   | otherwise = Reft (v', subst1 ras (v, EVar v'))


addIds = zipWith (\i c -> (i, shiftId i $ c {sid = Just i})) [1..]
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
                   , q_pos    :: !SourcePos       -- ^ Source Location
                   }
               deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance Fixpoint Qualifier where
  toFix = pprQual

instance NFData Qualifier where
  rnf (Q x1 x2 x3 _) = rnf x1 `seq` rnf x2 `seq` rnf x3

pprQual (Q n xts p l) = text "qualif" <+> text (symbolString n) <> parens args <> colon <+> toFix p <+> text "//" <+> toFix l
  where
    args              = intersperse comma (toFix <$> xts)

------------------------------------------------------------------------
----------------- Top-Level Constraint System --------------------------
------------------------------------------------------------------------

data FInfo a = FI { cm    :: M.HashMap Integer (SubC a)
                  , ws    :: ![WfC a]
                  , bs    :: !BindEnv
                  , gs    :: !FEnv
                  , lits  :: ![(Symbol, Sort)]
                  , kuts  :: Kuts
                  , quals :: ![Qualifier]
                  }
               deriving (Show)

toFixpoint x' = kutsDoc x' $+$ gsDoc x' $+$ conDoc x' $+$ bindsDoc x' $+$ csDoc x' $+$ wsDoc x'
  where
    conDoc    = vcat     . map toFixConstant . lits
    csDoc     = vcat     . map toFix . M.elems . cm
    wsDoc     = vcat     . map toFix . ws
    kutsDoc   = toFix    . kuts
    bindsDoc  = toFix    . bs
    gsDoc     = toFixGs  . gs

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

-- NUKE isTautoReft :: Reft -> Bool
-- NUKE isTautoReft (Reft (_, ra)) = isTautoRa ra
-- NUKE
-- NUKE isTautoRa :: Refa -> Bool
-- NUKE isTautoRa = isTautoPred . raPred


instance Reftable Reft where
  isTauto  = isTautoPred . reftPred
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
  isFalse (Reft(_, (Refa p))) = isFalse p

---------------------------------------------------------------
-- | String Constants -----------------------------------------
---------------------------------------------------------------

symConstLits    :: FInfo a -> [(Symbol, Sort)]
symConstLits fi = [(encodeSymConst c, sortSymConst c) | c <- symConsts fi]

-- | Replace all symbol-representations-of-string-literals with string-literal
--   Used to transform parsed output from fixpoint back into fq.


instance Symbolic SymConst where
  symbol = encodeSymConst

encodeSymConst        :: SymConst -> Symbol
encodeSymConst (SL s) = symbol $ litPrefix `mappend` s

sortSymConst          :: SymConst -> Sort
sortSymConst (SL _)   = strSort

decodeSymConst :: Symbol -> Maybe SymConst
decodeSymConst = fmap SL . T.stripPrefix litPrefix . symbolText

litPrefix    :: Text
litPrefix    = "lit" `T.snoc` symSepName

strSort      :: Sort
strSort      = FInt 

class SymConsts a where
  symConsts :: a -> [SymConst]

instance SymConsts (FInfo a) where
  symConsts fi = sortNub $ csLits ++ bsLits ++ gsLits ++ qsLits
    where
      csLits   = concatMap symConsts                     $ M.elems  $  cm    fi
      bsLits   = concatMap symConsts $ map snd $ M.elems $ beBinds $  bs    fi
      gsLits   = concatMap symConsts $           M.elems $ seBinds $  gs    fi
      qsLits   = concatMap symConsts $                     q_body  <$> quals fi

instance SymConsts (SubC a) where
  symConsts c  = symConsts (sgrd c) ++
                 symConsts (slhs c) ++
                 symConsts (srhs c)

instance SymConsts SortedReft where
  symConsts = symConsts . sr_reft

instance SymConsts Reft where
  symConsts (Reft (_, ra)) = symConsts ra

instance SymConsts Refa where
  symConsts (Refa p)           = symConsts p

instance SymConsts Expr where
  symConsts (ESym c)       = [c]
  symConsts (EApp _ es)    = concatMap symConsts es
  symConsts (ENeg e)       = symConsts e
  symConsts (EBin _ e e')  = concatMap symConsts [e, e']
  symConsts (EIte p e e')  = symConsts p ++ concatMap symConsts [e, e']
  symConsts (ECst e _)     = symConsts e
  symConsts _              = []

instance SymConsts Pred where
  symConsts (PNot p)           = symConsts p
  symConsts (PAnd ps)          = concatMap symConsts ps
  symConsts (POr ps)           = concatMap symConsts ps
  symConsts (PImp p q)         = concatMap symConsts [p, q]
  symConsts (PIff p q)         = concatMap symConsts [p, q]
  symConsts (PAll _ p)         = symConsts p
  symConsts (PBexp e)          = symConsts e
  symConsts (PAtom _ e e')     = concatMap symConsts [e, e']
  symConsts (PKVar _ (Su xes)) = concatMap symConsts $ snd <$> xes
  symConsts _                  = []

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

dummyLoc :: a -> Located a
dummyLoc = Loc l l where l = dummyPos "Fixpoint.Types.dummyLoc"

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

instance (NFData a) => NFData (Located a) where
  -- FIXME: no instance NFData SrcSpan
  rnf (Loc _ _  x) = rnf x
