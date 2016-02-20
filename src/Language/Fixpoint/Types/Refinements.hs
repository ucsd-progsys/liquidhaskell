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
{-# LANGUAGE PatternSynonyms            #-}

-- | This module contains the data types for representing terms in the
--   refinement logic; currently split into @Expr@ and @Pred@ but which
--   will be unified.

module Language.Fixpoint.Types.Refinements (

  -- * Representing Terms
    SymConst (..)
  , Constant (..)
  , Bop (..)
  , Brel (..)
  , Expr (..), Pred
  , pattern PTrue, pattern PTop, pattern PFalse, pattern EBot
  , KVar (..)
  , Subst (..)
  , Reft (..)
  , SortedReft (..)

  -- * Constructing Terms
  , eVar, elit
  , eProp
  , pAnd, pOr, pIte
  , isTautoPred

  -- * Generalizing Embedding with Typeclasses
  , Expression (..)
  , Predicate (..)
  , Subable (..)
  , Reftable (..)

  -- * Constructing Refinements
  , reft                    -- "smart
  , trueSortedReft          -- trivial reft
  , trueReft, falseReft     -- trivial reft
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
  , flattenRefas
  , conjuncts
  , mapPredReft
  , pprintReft
  , reftConjuncts
  , intKvar
  , vv_
  , mkEApp, eApps, splitEApp
  ) where

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           Data.Hashable
import           GHC.Generics              (Generic)
import           Data.List                 (partition) -- , foldl', sort, sortBy)
import           Data.String
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           Control.DeepSeq
import           Data.Maybe                (isJust)
-- import           Text.Printf               (printf)
-- import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.PrettyPrint
-- import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Misc
-- import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ
-- import           Data.Array                hiding (indices)
import qualified Data.HashMap.Strict       as M
-- import qualified Data.HashSet              as S

instance NFData KVar
instance NFData Subst
instance NFData Constant
instance NFData SymConst
instance NFData Brel
instance NFData Bop
instance NFData Expr
instance NFData Reft
instance NFData SortedReft

instance (Hashable k, Eq k, B.Binary k, B.Binary v) => B.Binary (M.HashMap k v) where
  put = B.put . M.toList
  get = M.fromList <$> B.get

instance B.Binary KVar
instance B.Binary Subst
instance B.Binary Constant
instance B.Binary SymConst
instance B.Binary Brel
instance B.Binary Bop
instance B.Binary Expr
instance B.Binary Reft
instance B.Binary SortedReft



reftConjuncts :: Reft -> [Reft]
reftConjuncts (Reft (v, ra)) = [Reft (v, ra') | ra' <- ras']
  where
    ras'                     = if null ps then ks else ((pAnd ps) : ks)
    (ks, ps)                 = partition isKvar $ refaConjuncts ra

isKvar :: Expr -> Bool
isKvar (PKVar _ _) = True
isKvar _           = False

refaConjuncts :: Expr -> [Expr]
refaConjuncts p = [p' | p' <- conjuncts p, not $ isTautoPred p']


--------------------------------------------------------------------------------
-- | Kvars ---------------------------------------------------------------------
--------------------------------------------------------------------------------

newtype KVar = KV { kv :: Symbol }
               deriving (Eq, Ord, Data, Typeable, Generic, IsString)


intKvar :: Integer -> KVar
intKvar = KV . intSymbol "k_"

instance Show KVar where
  show (KV x) = "$" ++ show x

instance Hashable KVar
instance Hashable Brel
instance Hashable Bop
instance Hashable SymConst
instance Hashable Constant

--------------------------------------------------------------------------------
-- | Substitutions -------------------------------------------------------------
--------------------------------------------------------------------------------

newtype Subst = Su (M.HashMap Symbol Expr)
                deriving (Eq, Data, Typeable, Generic)

instance Show Subst where
  show = showFix

instance Fixpoint Subst where
  toFix (Su m) = case hashMapToAscList m of
                   []  -> empty
                   xys -> hcat $ map (\(x,y) -> brackets $ toFix x <> text ":=" <> toFix y) xys

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

data Bop  = Plus | Minus | Times | Div | Mod | RTimes | RDiv 
            deriving (Eq, Ord, Show, Data, Typeable, Generic)
              -- NOTE: For "Mod" 2nd expr should be a constant or a var *)

data Expr = ESym !SymConst
          | ECon !Constant
          | EVar !Symbol
          -- NV TODO: change this to `EApp !Expr !Expr`
          | EApp !Expr !Expr
          | ENeg !Expr
          | EBin !Bop !Expr !Expr
          | EIte !Expr !Expr !Expr
          | ECst !Expr !Sort
          | ELam !(Symbol, Sort)   !Expr
          | ETApp !Expr !Sort 
          | ETAbs !Expr !Symbol

--- Used to be predicates
          | PAnd   ![Expr]
          | POr    ![Expr]
          | PNot   !Expr
          | PImp   !Expr !Expr
          | PIff   !Expr !Expr
          | PAtom  !Brel  !Expr !Expr
          | PKVar  !KVar !Subst
          | PAll   ![(Symbol, Sort)] !Expr
          | PExist ![(Symbol, Sort)] !Expr
          | PGrad
          deriving (Eq, Show, Data, Typeable, Generic)

type Pred = Expr

pattern PTrue  = PAnd []
pattern PTop   = PAnd []
pattern PFalse = POr []
pattern EBot   = POr []

mkEApp :: LocSymbol -> [Expr] -> Expr
mkEApp f = eApps (EVar $ val f)

eApps :: Expr -> [Expr] -> Expr
eApps f es  = foldl EApp f es

splitEApp :: Expr -> (Expr, [Expr])
splitEApp = go []
  where
    go acc (EApp f e) = go (e:acc) f
    go acc e          = (e, acc)


newtype Reft = Reft (Symbol, Expr)
               deriving (Eq, Data, Typeable, Generic)

data SortedReft = RR { sr_sort :: !Sort, sr_reft :: !Reft }
                  deriving (Eq, Data, Typeable, Generic)

elit :: Located Symbol -> Sort -> Expr
elit l s = ECon $ L (symbolText $ val l) s

instance Fixpoint Constant where
  toFix (I i)   = toFix i
  toFix (R i)   = toFix i
  toFix (L s t) = parens $ text "lit" <+> text "\"" <> toFix s <> text "\"" <+> toFix t

---------------------------------------------------------------
-- | String Constants -----------------------------------------
---------------------------------------------------------------

-- | Replace all symbol-representations-of-string-literals with string-literal
--   Used to transform parsed output from fixpoint back into fq.

instance Symbolic SymConst where
  symbol = encodeSymConst

encodeSymConst        :: SymConst -> Symbol
encodeSymConst (SL s) = litSymbol $ symbol s

decodeSymConst :: Symbol -> Maybe SymConst
decodeSymConst = fmap (SL . symbolText) . unLitSymbol

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
  toFix Plus   = text "+"
  toFix Minus  = text "-"
  toFix RTimes = text "*."
  toFix Times  = text "*"
  toFix Div    = text "/"
  toFix RDiv   = text "/."
  toFix Mod    = text "mod"

instance Fixpoint Expr where
  toFix (ESym c)       = toFix $ encodeSymConst c
  toFix (ECon c)       = toFix c
  toFix (EVar s)       = toFix s
  toFix e@(EApp _ _)   = parens $ hcat $ punctuate " " $ toFix <$> (f:es) where (f, es) = splitEApp e
  toFix (ENeg e)       = parens $ text "-"  <+> parens (toFix e)
  toFix (EBin o e1 e2) = parens $ toFix e1  <+> toFix o <+> toFix e2
  toFix (EIte p e1 e2) = parens $ text "if" <+> toFix p <+> text "then" <+> toFix e1 <+> text "else" <+> toFix e2
  toFix (ECst e so)    = parens $ toFix e   <+> text " : " <+> toFix so
  -- toFix (EBot)         = text "_|_"
  -- toFix PTop           = text "???"
  toFix PTrue          = text "true"
  toFix PFalse         = text "false"
  toFix (PNot p)       = parens $ text "~" <+> parens (toFix p)
  toFix (PImp p1 p2)   = parens $ toFix p1 <+> text "=>" <+> toFix p2
  toFix (PIff p1 p2)   = parens $ toFix p1 <+> text "<=>" <+> toFix p2
  toFix (PAnd ps)      = text "&&" <+> toFix ps
  toFix (POr  ps)      = text "||" <+> toFix ps
  toFix (PAtom r e1 e2)  = parens $ toFix e1 <+> toFix r <+> toFix e2
  toFix (PKVar k su)     = toFix k <> toFix su
  toFix (PAll xts p)     = "forall" <+> (toFix xts
                                        $+$ ("." <+> toFix p))
  toFix (PExist xts p)   = "exists" <+> (toFix xts
                                        $+$ ("." <+> toFix p))
  toFix (ETApp e s)      = text "tapp" <+> toFix e <+> toFix s
  toFix (ETAbs e s)      = text "tabs" <+> toFix e <+> toFix s
  toFix PGrad            = text "??"
  toFix (ELam (x,s) e)   = text "lam" <+> toFix x <+> ":" <+> toFix s <+> "." <+> toFix e 

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

isContraPred   :: Expr -> Bool
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

isTautoPred   :: Expr -> Bool
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

opPrec Mod    = 5
opPrec Plus   = 6
opPrec Minus  = 6
opPrec Times  = 7
opPrec RTimes = 7
opPrec Div    = 7
opPrec RDiv   = 7

instance PPrint Expr where
  pprintPrec _ (ESym c)        = pprint c
  pprintPrec _ (ECon c)        = pprint c
  pprintPrec _ (EVar s)        = pprint s
  -- pprintPrec _ (EBot)          = text "_|_"
  pprintPrec z (ENeg e)        = parensIf (z > zn) $
                                   text "-" <> pprintPrec (zn+1) e
    where zn = 2
  pprintPrec z (EApp f es)     = parensIf (z > za) $
                                   pprint f <+> (pprintPrec (za+1) es)
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

  -- pprintPrec _ PTop            = text "???"
  pprintPrec _ PTrue           = trueD
  pprintPrec _ PFalse          = falseD
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
                                   pprintBin (za + 1) trueD andD ps
    where za = 3
  pprintPrec z (POr  ps)       = parensIf (z > zo) $
                                   pprintBin (zo + 1) falseD orD  ps
    where zo = 3
  pprintPrec z (PAtom r e1 e2) = parensIf (z > za) $
                                   pprintPrec (za+1) e1 <+>
                                   pprint r             <+>
                                   pprintPrec (za+1) e2
    where za = 4
  pprintPrec _ (PAll xts p)    = pprintQuant "forall" xts p
  pprintPrec _ (PExist xts p)  = pprintQuant "exists" xts p
  pprintPrec _ (ELam (x,t) e)  = text "lam" <+> toFix x <+> ":" <+> toFix t <+> text "." <+> pprint e
  pprintPrec _ p@(PKVar {})    = toFix p
  pprintPrec _ (ETApp e s)     = text "ETApp" <+> toFix e <+> toFix s
  pprintPrec _ (ETAbs e s)     = text "ETAbs" <+> toFix e <+> toFix s
  pprintPrec _ PGrad           = text "?"

pprintQuant d xts p = (d <+> toFix xts)
                      $+$
                      ("  ." <+> pprint p)

trueD  = "true"
falseD = "false"
andD   = "&&"
orD    = "||"

pprintBin _ b _ [] = b
pprintBin z _ o xs = vIntersperse o $ pprintPrec z <$> xs

vIntersperse _ []     = empty
vIntersperse _ [d]    = d
vIntersperse s (d:ds) = vcat (d : ((s <+>) <$> ds))

pprintReft :: Reft -> Doc
pprintReft (Reft (_,ra)) = pprintBin z trueD andD flat
  where
    flat = flattenRefas [ra]
    z    = if length flat > 1 then 3 else 0

------------------------------------------------------------------------
-- | Generalizing Symbol, Expression, Predicate into Classes -----------
------------------------------------------------------------------------

-- | Values that can be viewed as Constants

-- | Values that can be viewed as Expressions

class Expression a where
  expr   :: a -> Expr

-- | Values that can be viewed as Predicates

class Predicate a where
  prop   :: a -> Expr

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

instance Predicate Expr where
  prop = id

instance Predicate Bool where
  prop True  = PTrue
  prop False = PFalse

instance Expression a => Expression (Located a) where
  expr   = expr . val

eVar ::  Symbolic a => a -> Expr
eVar = EVar . symbol

eProp ::  Symbolic a => a -> Expr
eProp = mkProp . eVar

isSingletonExpr :: Symbol -> Expr -> Maybe Expr
isSingletonExpr v (PAtom r e1 e2)
  | e1 == EVar v && isEq r = Just e2
  | e2 == EVar v && isEq r = Just e1
isSingletonExpr _ _        = Nothing

pAnd, pOr     :: ListNE Expr -> Expr
pAnd          = simplify . PAnd
pOr           = simplify . POr
pIte p1 p2 p3 = pAnd [p1 `PImp` p2, (PNot p1) `PImp` p3]
mkProp        = EApp (EVar propConName)


--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------

isSingletonReft :: Reft -> Maybe Expr
isSingletonReft (Reft (v, ra)) = firstMaybe (isSingletonExpr v) $ conjuncts ra

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

reft :: Symbol -> Expr -> Reft
reft v p = Reft (v, p)

mapPredReft :: (Expr -> Expr) -> Reft -> Reft
mapPredReft f (Reft (v, p)) = Reft (v, f p)

---------------------------------------------------------------
-- | Refinements ----------------------------------------------
---------------------------------------------------------------

isFunctionSortedReft :: SortedReft -> Bool
isFunctionSortedReft = isJust . functionSort . sr_sort

isNonTrivial :: Reftable r => r -> Bool
isNonTrivial = not . isTauto

reftPred :: Reft -> Expr
reftPred (Reft (_, p)) = p

reftBind :: Reft -> Symbol
reftBind (Reft (x, _)) = x

------------------------------------------------------------
-- | Generally Useful Refinements --------------------------
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

flattenRefas :: [Expr] -> [Expr]
flattenRefas        = concatMap flatP
  where
    flatP (PAnd ps) = concatMap flatP ps
    flatP p         = [p]

conjuncts :: Expr -> [Expr]
conjuncts (PAnd ps) = concatMap conjuncts ps
conjuncts p
  | isTautoPred p   = []
  | otherwise       = [p]

-------------------------------------------------------------------------
-- | TODO: This doesn't seem to merit a TC ------------------------------
-------------------------------------------------------------------------

class Falseable a where
  isFalse :: a -> Bool

instance Falseable Expr where
  isFalse (PFalse) = True
  isFalse _        = False

instance Falseable Reft where
  isFalse (Reft (_, ra)) = isFalse ra

-------------------------------------------------------------------------
-- | Class Predicates for Valid Refinements -----------------------------
-------------------------------------------------------------------------

class Subable a where
  syms   :: a -> [Symbol]
  substa :: (Symbol -> Symbol) -> a -> a
  -- substa f  = substf (EVar . f)

  substf :: (Symbol -> Expr) -> a -> a
  subst  :: Subst -> a -> a
  subst1 :: a -> (Symbol, Expr) -> a
  subst1 y (x, e) = subst (Su $ M.fromList [(x,e)]) y

instance Subable a => Subable (Located a) where
  syms (Loc _ _ x)   = syms x
  substa f (Loc l l' x) = Loc l l' (substa f x)
  substf f (Loc l l' x) = Loc l l' (substf f x)
  subst su (Loc l l' x) = Loc l l' (subst su x)


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
