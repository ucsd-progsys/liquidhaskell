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

-- | This module contains the data types for representing terms in the
--   refinement logic; currently split into @Expr@ and @Pred@ but which
--   will be unified.

module Language.Fixpoint.Types.Refinements (

  -- * Representing Terms
    SymConst (..)
  , Constant (..)
  , Bop (..)
  , Brel (..)
  , Expr (..)
  , Pred (..)
  , KVar (..)

  -- * Constructing Terms
  , eVar, elit
  , eProp
  , pAnd, pOr, pIte
  , isTautoPred

  -- * Generalizing Embedding with Typeclasses
  , Expression (..)
  , Predicate (..)

  -- * Substitutions
  , Subst (..)
  , Subable (..)
  , mkSubst
  , isEmptySubst
  , substExcept
  , substfExcept
  , subst1Except
  , targetSubstSyms

  ) where

import           Debug.Trace               (trace)

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           Data.Hashable
import           GHC.Generics              (Generic)
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

--------------------------------------------------------------------------------
-- | Kvars ---------------------------------------------------------------------
--------------------------------------------------------------------------------

newtype KVar = KV {kv :: Symbol }
               deriving (Eq, Ord, Data, Typeable, Generic, IsString)

intKvar :: Integer -> KVar
intKvar = KV . intSymbol "k_"

instance Show KVar where
  show (KV x) = "$" ++ show x

instance Hashable KVar


--------------------------------------------------------------------------------
-- | Substitutions -------------------------------------------------------------
--------------------------------------------------------------------------------

newtype Subst = Su (M.HashMap Symbol Expr)
                deriving (Eq, Data, Typeable, Generic)

class Subable a where
  syms   :: a -> [Symbol]
  substa :: (Symbol -> Symbol) -> a -> a
  -- substa f  = substf (EVar . f)

  substf :: (Symbol -> Expr) -> a -> a
  subst  :: Subst -> a -> a
  subst1 :: a -> (Symbol, Expr) -> a
  subst1 y (x, e) = subst (Su $ M.fromList [(x,e)]) y

appSubst :: Subst -> Symbol -> Expr
appSubst (Su s) x = fromMaybe (EVar x) (M.lookup x s)

instance Monoid Subst where
  mempty  = emptySubst
  mappend = catSubst

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

--------------------------------------------------------------------------------
-- | Substitutions -------------------------------------------------------------
--------------------------------------------------------------------------------

instance Subable () where
  syms _      = []
  subst _ ()  = ()
  substf _ () = ()
  substa _ () = ()

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
  subst su (PExist bs p)
          | disjoint su bs = PExist bs $ subst su p --(substExcept su (fst <$> bs)) p
          | otherwise      = errorstar "subst: EXISTS (without disjoint binds)"
  subst _  p               = p

disjoint :: Subst -> [(Symbol, Sort)] -> Bool
disjoint (Su su) bs = S.null $ suSyms `S.intersection` bsSyms
  where
    suSyms = S.fromList $ (syms $ M.elems su) ++ (syms $ M.keys su)
    bsSyms = S.fromList $ syms $ fst <$> bs


--------------------------------------------------------------------------------
-- | Expressions ---------------------------------------------------------------
--------------------------------------------------------------------------------

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
          | EApp !LocSymbol ![Expr]
          | ENeg !Expr
          | EBin !Bop !Expr !Expr
          | EIte !Pred !Expr !Expr
          | ECst !Expr !Sort
          | EBot
          deriving (Eq, Show, Data, Typeable, Generic)

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



elit :: Located Symbol -> Sort -> Expr
elit l s = ECon $ L (symbolText $ val l) s

instance Fixpoint Constant where
  toFix (I i)   = toFix i
  toFix (R i)   = toFix i
  toFix (L s t) = parens $ text "lit" <+> text "\"" <> toFix s <> text "\"" <+> toFix t

instance Fixpoint SymConst where
  toFix  = toFix . encodeSymConst

instance Fixpoint KVar where
  toFix (KV k) = text "$" <> toFix k

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
  toFix (EApp f es)    = toFix f <> parens (toFix es)
  toFix (ENeg e)       = parens $ text "-"  <+> parens (toFix e)
  toFix (EBin o e1 e2) = parens $ toFix e1  <+> toFix o <+> toFix e2
  toFix (EIte p e1 e2) = parens $ text "if" <+> toFix p <+> text "then" <+> toFix e1 <+> text "else" <+> toFix e2
  toFix (ECst e so)    = parens $ toFix e   <+> text " : " <+> toFix so
  toFix (EBot)         = text "_|_"


instance PPrint Constant where
  pprint = toFix

instance PPrint Brel where
  pprint Eq = text "=="
  pprint Ne = text "/="
  pprint r  = toFix r

instance PPrint Bop where
  pprint  = toFix

instance PPrint Sort where
  pprint = toFix

instance PPrint KVar where
  pprint (KV x) = text "$" <> pprint x

instance PPrint SymConst where
  pprint (SL x) = doubleQuotes $ text $ T.unpack x

-- | Wrap the enclosed 'Doc' in parentheses only if the condition holds.
parensIf True  = parens
parensIf False = id

-- NOTE: The following Expr and Pred printers use pprintPrec to print
-- expressions with minimal parenthesization. The precedence rules are somewhat
-- fragile, and it would be nice to have them directly tied to the parser, but
-- the general idea is (from lowest to highest precedence):
--
-- 1 - if-then-else
-- 2 - => and <=>
-- 3 - && and ||
-- 4 - ==, !=, <, <=, >, >=
-- 5 - mod
-- 6 - + and -
-- 7 - * and /
-- 8 - function application
--
-- Each printer `p` checks whether the precedence of the context is greater than
-- its own precedence. If so, the printer wraps itself in parentheses. Then it
-- sets the contextual precedence for recursive printer invocations to
-- (prec p + 1).

opPrec Mod   = 5
opPrec Plus  = 6
opPrec Minus = 6
opPrec Times = 7
opPrec Div   = 7

instance PPrint Expr where
  pprintPrec _ (ESym c)        = pprint c
  pprintPrec _ (ECon c)        = pprint c
  pprintPrec _ (EVar s)        = pprint s
  pprintPrec _ (EBot)          = text "_|_"
  pprintPrec z (ENeg e)        = parensIf (z > zn) $
                                   text "-" <> pprintPrec (zn+1) e
    where zn = 2
  pprintPrec z (EApp f es)     = parensIf (z > za) $
                                   intersperse empty $
                                     pprint f : (pprintPrec (za+1) <$> es)
    where za = 8
  pprintPrec z (EBin o e1 e2)  = parensIf (z > zo) $
                                   pprintPrec (zo+1) e1 <+>
                                   pprint o             <+>
                                   pprintPrec (zo+1) e2
    where zo = opPrec o
  pprintPrec z (EIte p e1 e2)  = parensIf (z > zi) $
                                   text "if"   <+> pprintPrec (zi+1) p  <+>
                                   text "then" <+> pprintPrec (zi+1) e1 <+>
                                   text "else" <+> pprintPrec (zi+1) e2
    where zi = 1
  pprintPrec _ (ECst e so)     = parens $ pprint e <+> text ":" <+> pprint so

instance PPrint Pred where
  pprintPrec _ PTop            = text "???"
  pprintPrec _ PTrue           = trueD
  pprintPrec _ PFalse          = falseD
  pprintPrec z (PBexp e)       = pprintPrec z e
  pprintPrec z (PNot p)        = parensIf (z > zn) $
                                   text "not" <+> pprintPrec (zn+1) p
    where zn = 8
  pprintPrec z (PImp p1 p2)    = parensIf (z > zi) $
                                   (pprintPrec (zi+1) p1) <+>
                                   text "=>"              <+>
                                   (pprintPrec (zi+1) p2)
    where zi = 2
  pprintPrec z (PIff p1 p2)    = parensIf (z > zi) $
                                   (pprintPrec (zi+1) p1) <+>
                                   text "<=>"             <+>
                                   (pprintPrec (zi+1) p2)
    where zi = 2
  pprintPrec z (PAnd ps)       = parensIf (z > za) $
                                   pprintBin (za+1) trueD  andD ps
    where za = 3
  pprintPrec z (POr  ps)       = parensIf (z > zo) $
                                   pprintBin (zo+1) falseD orD  ps
    where zo = 3
  pprintPrec z (PAtom r e1 e2) = parensIf (z > za) $
                                   pprintPrec (za+1) e1 <+>
                                   pprint r             <+>
                                   pprintPrec (za+1) e2
    where za = 4
  pprintPrec _ (PAll xts p)    = text "forall" <+> toFix xts <+> text "." <+> pprint p
  pprintPrec _ (PExist xts p)  = text "exists" <+> toFix xts <+> text "." <+> pprint p
  pprintPrec _ p@(PKVar {})    = toFix p

trueD  = text "true"
falseD = text "false"
andD   = text " &&"
orD    = text " ||"

pprintBin _ b _ [] = b
pprintBin z _ o xs = intersperse o $ pprintPrec z <$> xs
