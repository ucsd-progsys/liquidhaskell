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
--   constraints in Haskell.

module Language.Fixpoint.Types (

    module Language.Fixpoint.Types.PrettyPrint
  , module Language.Fixpoint.Types.Spans
  , module Language.Fixpoint.Types.Errors
  , module Language.Fixpoint.Types.Names
  , module Language.Fixpoint.Types.Sorts
  , module Language.Fixpoint.Types.Refinements

  , toFixpoint
  , writeFInfo
  , FInfo, SInfo, GInfo (..)
  , fi


  -- * Constraints
  , WfC (..)
  , SubC, subcId, sid, senv, slhs, srhs, subC, wfC
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

  -- * Qualifiers
  , Qualifier (..)

  -- * Refinements
  , SortedReft (..), Reft(..), Reftable(..)

  -- * Constructing Refinements
  , reft                    -- "smart
  , trueSortedReft          -- trivial reft
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

  -- * Cut KVars
  , Kuts (..)
  , ksEmpty
  , ksUnion
  , ksMember

  -- * FInfo to SInfo format conversion
  , convertFormat
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
import           Control.DeepSeq
import           Data.Maybe                (isJust, mapMaybe, listToMaybe, fromMaybe)
import           Text.Printf               (printf)
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Utils.Misc
import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ

import           Data.Array                hiding (indices)
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S

exprSymbols :: Expr -> [Symbol]
exprSymbols = go
  where
    go (EVar x)        = [x]
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

--------------------------------------------------------------------------------
-- | Type Constructors ---------------------------------------------------------
--------------------------------------------------------------------------------


instance Show Subst where
  show = showFix

instance Fixpoint Subst where
  toFix (Su m) = case hashMapToAscList m of
                   []  -> empty
                   xys -> hcat $ map (\(x,y) -> brackets $ toFix x <> text ":=" <> toFix y) xys

targetSubstSyms :: Subst -> [Symbol]
targetSubstSyms (Su ms) = syms $ M.elems ms

instance PPrint Reft where
  pprint r@(Reft (_,ra))
    | isTauto r        = text "true"
    | otherwise        = {- intersperse comma -} pprintBin z trueD andD flat
    where
      flat = flattenRefas [ra]
      z    = if length flat > 1 then 3 else 0

instance PPrint SortedReft where
  pprint (RR so (Reft (v, ras)))
    = braces
    $ pprint v <+> text ":" <+> toFix so <+> text "|" <+> pprint ras

instance PPrint a => PPrint (Located a) where
  pprint (Loc _ _ x) = pprint x


instance PTable (SInfo a) where
  ptable fi = DocTable [ (text "# Sub Constraints", pprint $ length $ cm fi)
                       , (text "# WF  Constraints", pprint $ length $ ws fi)
                       ]

--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------


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
    eqT (PAnd [])
               = True
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
isSingletonReft (Reft (v, ra)) = firstMaybe (isSingletonExpr v) $ conjuncts ra

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

pAnd, pOr     :: ListNE Pred -> Pred
pAnd          = simplify . PAnd
pOr           = simplify . POr
pIte p1 p2 p3 = pAnd [p1 `PImp` p2, (PNot p1) `PImp` p3]

mkProp        = PBexp . EApp (dummyLoc propConName) . (: [])

pprReft (Reft (v, p)) d
  | isTautoPred p
  = d
  | otherwise
  = braces (toFix v <+> colon <+> d <+> text "|" <+> ppRas [p])

pprReftPred (Reft (_, p))
  | isTautoPred p
  = text "true"
  | otherwise
  = ppRas [p]

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
relReft r e   = Reft (vv_, PAtom r (eVar vv_)  (expr e))

exprReft, notExprReft, uexprReft ::  (Expression a) => a -> Reft
exprReft      = relReft Eq
notExprReft   = relReft Ne
uexprReft     = relReft Ueq

propReft      ::  (Predicate a) => a -> Reft
propReft p    = Reft (vv_, PIff (eProp vv_) (prop p))

predReft      :: (Predicate a) => a -> Reft
predReft p    = Reft (vv_, prop p)

reft :: Symbol -> Pred -> Reft
reft v p = Reft (v, p)

mapPredReft :: (Pred -> Pred) -> Reft -> Reft
mapPredReft f (Reft (v, p)) = Reft (v, f p)


---------------------------------------------------------------
----------------- Refinements ---------------------------------
---------------------------------------------------------------

newtype Reft = Reft (Symbol, Pred)
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

reftPred :: Reft -> Pred
reftPred (Reft (_, p)) = p

reftBind :: Reft -> Symbol
reftBind (Reft (x, _)) = x


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

instance Fixpoint Reft where
  toFix = pprReftPred

instance Fixpoint SortedReft where
  toFix (RR so (Reft (v, ra)))
    = braces
    $ toFix v <+> text ":" <+> toFix so <+> text "|" <+> (toFix $ conjuncts ra)

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
type BindMap a     = M.HashMap BindId a

newtype IBindEnv   = FB (S.HashSet BindId) deriving (Eq, Data, Typeable, Generic)

newtype SEnv a     = SE { seBinds :: M.HashMap Symbol a }
                     deriving (Eq, Data, Typeable, Generic, Foldable, Traversable)

data SizedEnv a    = BE { beSize  :: Int
                        , beBinds :: BindMap a
                        } deriving (Eq, Show, Functor, Foldable, Generic, Traversable)

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
                   , wrft  :: (Symbol, Sort, KVar)
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
  -- mappend u@(UnknownError _) _    = u
  -- mappend _ u@(UnknownError _)    = u

instance Functor FixResult where
  fmap f (Crash xs msg)   = Crash (f <$> xs) msg
  fmap f (Unsafe xs)      = Unsafe (f <$> xs)
  fmap _ Safe             = Safe
  -- fmap _ (UnknownError d) = UnknownError d

instance (Ord a, Fixpoint a) => Fixpoint (FixResult (SubC a)) where
  toFix Safe             = text "Safe"
  -- toFix (UnknownError d) = text $ "Unknown Error: " ++ d
  toFix (Crash xs msg)   = vcat $ [ text "Crash!" ] ++  pprSinfos "CRASH: " xs ++ [parens (text msg)]
  toFix (Unsafe xs)      = vcat $ text "Unsafe:" : pprSinfos "WARNING: " xs


pprSinfos :: (Ord a, Fixpoint a) => String -> [SubC a] -> [Doc]
pprSinfos msg = map ((text msg <>) . toFix) . sort . fmap sinfo

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
     where bd =   toFix (senv c)
              $+$ text "lhs" <+> toFix (slhs c)
              $+$ text "rhs" <+> toFix (srhs c)
              $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "constraint" <+> pprId (sid c)) (toFix (sinfo c))

instance Fixpoint a => Fixpoint (SimpC a) where
  toFix c     = hang (text "\n\nsimpleConstraint:") 2 bd
     where bd =   toFix (senv c)
              $+$ text "rhs" <+> toFix (crhs c)
              $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "simpleConstraint" <+> pprId (sid c)) (toFix (sinfo c))

instance Fixpoint a => Fixpoint (WfC a) where
  toFix w     = hang (text "\n\nwf:") 2 bd
    where bd  =   toFix (wenv w)
              -- NOTE: this next line is printed this way for compatability with the OCAML solver
              $+$ text "reft" <+> toFix (RR t (Reft (v, PKVar k emptySubst)))
              $+$ toFixMeta (text "wf") (toFix (winfo w))
          (v, t, k) = wrft w

toFixMeta :: Doc -> Doc -> Doc
toFixMeta k v = text "// META" <+> k <+> text ":" <+> v
             --  $+$ text "\n"

pprId (Just i)  = text "id" <+> tshow i
pprId _         = text ""

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
trueReft  = Reft (vv_, PTrue)
falseReft = Reft (vv_, PFalse)

flattenRefas :: [Pred] -> [Pred]
flattenRefas        = concatMap flatP
  where
    flatP (PAnd ps) = concatMap flatP ps
    flatP p         = [p]

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



instance (Hashable a, Eq a, B.Binary a) => B.Binary (S.HashSet a) where
  put = B.put . S.toList
  get = S.fromList <$> B.get

instance (Hashable k, Eq k, B.Binary k, B.Binary v) => B.Binary (M.HashMap k v) where
  put = B.put . M.toList
  get = M.fromList <$> B.get

instance B.Binary KVar
instance B.Binary Kuts
instance B.Binary Qualifier


instance B.Binary Subst
instance B.Binary IBindEnv
instance B.Binary BindEnv
instance B.Binary Constant
instance B.Binary SymConst
instance B.Binary Brel
instance B.Binary Bop
instance B.Binary Expr
instance B.Binary Pred
instance B.Binary Reft
instance B.Binary SortedReft
instance (B.Binary a) => B.Binary (SEnv a)
instance (B.Binary a) => B.Binary (FixResult a)
instance (B.Binary a) => B.Binary (SubC a)
instance (B.Binary a) => B.Binary (WfC a)
instance (B.Binary a) => B.Binary (SimpC a)
instance (B.Binary (c a), B.Binary a) => B.Binary (GInfo c a)

----------------------------------------------------------------
-- | Strictness ------------------------------------------------
----------------------------------------------------------------

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
instance NFData Reft
instance NFData SortedReft
instance (NFData a) => NFData (SEnv a)
instance (NFData a) => NFData (SubC a)
instance (NFData a) => NFData (WfC a)
instance (NFData a) => NFData (SimpC a)
instance (NFData (c a), NFData a) => NFData (GInfo c a)
instance (NFData a) => NFData (Result a)
instance (NFData a) => NFData (WrappedC a) where
  rnf (WrapC _) = ()

---------------------------------------------------------------------------
-------- Constraint Constructor Wrappers ----------------------------------
---------------------------------------------------------------------------

wfC :: IBindEnv -> SortedReft -> a -> [WfC a]
wfC be sr x
  | Reft (v, PKVar k su) <- sr_reft sr
              = if isEmptySubst su
                   then [WfC be (v, sr_sort sr, k) x]
                   else err
  | otherwise = []
  where
    err       = errorstar $ "wfKvar: malformed wfC " ++ show sr

subC :: IBindEnv -> SortedReft -> SortedReft -> Maybe Integer -> Tag -> a -> [SubC a]
subC γ sr1 sr2 i y z = [SubC γ sr1' (sr2' r2') i y z | r2' <- reftConjuncts r2]
   where
     RR t1 r1          = sr1
     RR t2 r2          = sr2
     sr1'              = RR t1 $ shiftVV r1  vv'
     sr2' r2'          = RR t2 $ shiftVV r2' vv'
     vv'               = mkVV i

reftConjuncts :: Reft -> [Reft]
reftConjuncts (Reft (v, ra)) = [Reft (v, ra') | ra' <- ras']
  where
    ras'                     = if null ps then ks else ((pAnd ps) : ks)
    (ks, ps)                 = partition isKvar $ refaConjuncts ra

isKvar :: Pred -> Bool
isKvar (PKVar _ _) = True
isKvar _           = False


refaConjuncts :: Pred -> [Pred]
refaConjuncts p              = [p' | p' <- conjuncts p, not $ isTautoPred p']

mkVV :: Maybe Integer -> Symbol
mkVV (Just i)  = vv $ Just i
mkVV Nothing   = vvCon

envCs :: BindEnv -> IBindEnv -> [(Symbol, SortedReft)]
envCs be env = [lookupBindEnv i be | i <- elemsIBindEnv env]

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
                   , q_pos    :: !SourcePos       -- ^ Source Location
                   }
               deriving (Eq, Show, Data, Typeable, Generic)

instance Loc Qualifier where
  srcSpan q = SS l l
    where
      l     = q_pos q

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

------------------------------------------------------------------------
-- | Constructing an FInfo
------------------------------------------------------------------------
fi cs ws binds ls ks qs bi fn
  = FI { cm       = M.fromList $ addIds cs
       , ws       = M.fromListWith err [(k, w) | w <- ws, let (_, _, k) = wrft w]
       , bs       = binds
       , lits     = ls
       , kuts     = ks
       , quals    = qs
       , bindInfo = bi
       , fileName = fn
       }
  where
    --TODO handle duplicates gracefully instead (merge envs by intersect?)
    err = errorstar "multiple WfCs with same kvar"

type FInfo a   = GInfo SubC a
type SInfo a   = GInfo SimpC a
data GInfo c a =
  FI { cm       :: M.HashMap Integer (c a)
     , ws       :: M.HashMap KVar (WfC a)
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
    wsDoc         = vcat     . map toFix . M.elems . ws
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

instance Monoid Reft where
  mempty  = trueReft
  mappend = meetReft

meetReft (Reft (v, ra)) (Reft (v', ra'))
  | v == v'          = Reft (v , ra  `mappend` ra')
  | v == dummySymbol = Reft (v', ra' `mappend` (ra `subst1`  (v , EVar v')))
  | otherwise        = Reft (v , ra  `mappend` (ra' `subst1` (v', EVar v )))

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
  ofReft   = errorstar "No instance of ofReft for SortedReft"
  params _ = []
  bot s    = s { sr_reft = falseReft }

class Falseable a where
  isFalse :: a -> Bool

instance Falseable Pred where
  isFalse (PFalse) = True
  isFalse _        = False

instance Falseable Reft where
  isFalse (Reft (_, ra)) = isFalse ra

---------------------------------------------------------------
-- | String Constants -----------------------------------------
---------------------------------------------------------------

-- | Replace all symbol-representations-of-string-literals with string-literal
--   Used to transform parsed output from fixpoint back into fq.


instance Symbolic SymConst where
  symbol = encodeSymConst

encodeSymConst        :: SymConst -> Symbol
encodeSymConst (SL s) = litPrefix `mappend` symbol s

decodeSymConst :: Symbol -> Maybe SymConst
decodeSymConst = fmap (SL . symbolText) . stripPrefix litPrefix

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

instance Expression a => Expression (Located a) where
  expr   = expr . val

instance Subable a => Subable (Located a) where
  syms (Loc _ _ x)   = syms x
  substa f (Loc l l' x) = Loc l l' (substa f x)
  substf f (Loc l l' x) = Loc l l' (substf f x)
  subst su (Loc l l' x) = Loc l l' (subst su x)

---------------------------------------------------------------------------
-- | FInfo to SInfo conversion
---------------------------------------------------------------------------
convertFormat :: (Fixpoint a) => FInfo a -> SInfo a
---------------------------------------------------------------------------
convertFormat fi = fi' { cm = subcToSimpc <$> cm fi' }
  where
    fi'          = M.foldlWithKey' blowOutVV fi $ cm fi

subcToSimpc :: SubC a -> SimpC a
subcToSimpc s = SimpC
  { _cenv     = senv s
  , _crhs     = reftPred $ sr_reft $ srhs s
  , _cid      = sid s
  , _ctag     = stag s
  , _cinfo    = sinfo s
  }

blowOutVV :: FInfo a -> Integer -> SubC a -> FInfo a
blowOutVV fi i subc = fi { bs = be', cm = cm' }
  where
    sr            = slhs subc
    x             = reftBind $ sr_reft sr
    (bindId, be') = insertBindEnv x sr $ bs fi
    subc'         = subc { _senv = insertsIBindEnv [bindId] $ senv subc }
    cm'           = M.insert i subc' $ cm fi
