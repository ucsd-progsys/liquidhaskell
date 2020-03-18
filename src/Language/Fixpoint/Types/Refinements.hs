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

-- | This module has the types for representing terms in the refinement logic.

module Language.Fixpoint.Types.Refinements (

  -- * Representing Terms
    SymConst (..)
  , Constant (..)
  , Bop (..)
  , Brel (..)
  , Expr (..), Pred
  , GradInfo (..)
  , pattern PTrue, pattern PTop, pattern PFalse, pattern EBot
  , pattern ETimes, pattern ERTimes, pattern EDiv, pattern ERDiv
  , pattern EEq
  , KVar (..)
  , Subst (..)
  , KVSub (..)
  , Reft (..)
  , SortedReft (..)

  -- * Constructing Terms
  , eVar, elit
  , eProp
  , pAnd, pOr, pIte
  , (&.&), (|.|)
  , pExist
  , mkEApp
  , mkProp
  , intKvar
  , vv_

  -- * Generalizing Embedding with Typeclasses
  , Expression (..)
  , Predicate (..)
  , Subable (..)
  , Reftable (..)

  -- * Constructors
  , reft                    -- "smart
  , trueSortedReft          -- trivial reft
  , trueReft, falseReft     -- trivial reft
  , exprReft                -- singleton: v == e
  , notExprReft             -- singleton: v /= e
  , uexprReft               -- singleton: v ~~ e
  , symbolReft              -- singleton: v == x
  , usymbolReft             -- singleton: v ~~ x
  , propReft                -- singleton: v <=> p
  , predReft                -- any pred : p
  , reftPred
  , reftBind

  -- * Predicates
  , isFunctionSortedReft, functionSort
  , isNonTrivial
  , isContraPred
  , isTautoPred
  , isSingletonExpr 
  , isSingletonReft
  , isFalse

  -- * Destructing
  , flattenRefas
  , conjuncts
  , eApps
  , eAppC
  , splitEApp
  , splitPAnd
  , reftConjuncts

  -- * Transforming
  , mapPredReft
  , pprintReft

  , debruijnIndex

  -- * Gradual Type Manipulation
  , pGAnds, pGAnd
  , HasGradual (..)
  , srcGradInfo

  ) where

import           Prelude hiding ((<>))
import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           Data.Hashable
import           GHC.Generics              (Generic)
import           Data.List                 (foldl', partition)
import           Data.String
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import qualified Data.HashMap.Strict       as M
import           Control.DeepSeq
import           Data.Maybe                (isJust)
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ.Compat

-- import           Text.Printf               (printf)


instance NFData KVar
instance NFData SrcSpan
instance NFData Subst
instance NFData GradInfo
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

instance (Eq a, Hashable a, B.Binary a) => B.Binary (TCEmb a) 
instance B.Binary SrcSpan
instance B.Binary KVar
instance B.Binary Subst
instance B.Binary GradInfo
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
    (ks, ps)                 = partition (\p -> isKvar p || isGradual p) $ refaConjuncts ra

isKvar :: Expr -> Bool
isKvar (PKVar _ _) = True
isKvar _           = False

class HasGradual a where
  isGradual :: a -> Bool
  gVars     :: a -> [KVar]
  gVars _ = [] 
  ungrad    :: a -> a
  ungrad x = x 

instance HasGradual Expr where
  isGradual (PGrad {}) = True
  isGradual (PAnd xs)  = any isGradual xs
  isGradual _          = False

  gVars (PGrad k _ _ _) = [k]
  gVars (PAnd xs)       = concatMap gVars xs
  gVars _               = []

  ungrad (PGrad {}) = PTrue
  ungrad (PAnd xs)  = PAnd (ungrad <$> xs )
  ungrad e          = e


instance HasGradual Reft where
  isGradual (Reft (_,r)) = isGradual r
  gVars (Reft (_,r))     = gVars r
  ungrad (Reft (x,r))    = Reft(x, ungrad r)

instance HasGradual SortedReft where
  isGradual = isGradual . sr_reft
  gVars     = gVars . sr_reft
  ungrad r  = r {sr_reft = ungrad (sr_reft r)}

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
instance Hashable GradInfo 
instance Hashable Subst 
instance Hashable Expr 
instance Hashable Reft

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
                   xys -> hcat $ map (\(x,y) -> brackets $ toFix x <-> text ":=" <-> toFix y) xys

instance PPrint Subst where
  pprintTidy _ = toFix

data KVSub = KVS
  { ksuVV    :: Symbol
  , ksuSort  :: Sort
  , ksuKVar  :: KVar
  , ksuSubst :: Subst
  } deriving (Eq, Data, Typeable, Generic, Show)

instance PPrint KVSub where
  pprintTidy k ksu = pprintTidy k (ksuVV ksu, ksuKVar ksu, ksuSubst ksu)

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
          | EApp !Expr !Expr
          | ENeg !Expr
          | EBin !Bop !Expr !Expr
          | EIte !Expr !Expr !Expr
          | ECst !Expr !Sort
          | ELam !(Symbol, Sort)   !Expr
          | ETApp !Expr !Sort
          | ETAbs !Expr !Symbol
          | PAnd   ![Expr]
          | POr    ![Expr]
          | PNot   !Expr
          | PImp   !Expr !Expr
          | PIff   !Expr !Expr
          | PAtom  !Brel  !Expr !Expr
          | PKVar  !KVar !Subst
          | PAll   ![(Symbol, Sort)] !Expr
          | PExist ![(Symbol, Sort)] !Expr
          | PGrad  !KVar !Subst !GradInfo !Expr
          | ECoerc !Sort !Sort !Expr  
          deriving (Eq, Show, Data, Typeable, Generic)

type Pred = Expr

pattern PTrue         = PAnd []
pattern PTop          = PAnd []
pattern PFalse        = POr  []
pattern EBot          = POr  []
pattern EEq e1 e2     = PAtom Eq    e1 e2
pattern ETimes e1 e2  = EBin Times  e1 e2
pattern ERTimes e1 e2 = EBin RTimes e1 e2
pattern EDiv e1 e2    = EBin Div    e1 e2
pattern ERDiv e1 e2   = EBin RDiv   e1 e2


data GradInfo = GradInfo {gsrc :: SrcSpan, gused :: Maybe SrcSpan}
          deriving (Eq, Show, Data, Typeable, Generic)

srcGradInfo :: SourcePos -> GradInfo
srcGradInfo src = GradInfo (SS src src) Nothing

mkEApp :: LocSymbol -> [Expr] -> Expr
mkEApp = eApps . EVar . val

eApps :: Expr -> [Expr] -> Expr
eApps f es  = foldl' EApp f es

splitEApp :: Expr -> (Expr, [Expr])
splitEApp = go []
  where
    go acc (EApp f e) = go (e:acc) f
    go acc e          = (e, acc)

splitPAnd :: Expr -> [Expr]
splitPAnd (PAnd es) = concatMap splitPAnd es
splitPAnd e         = [e]

eAppC :: Sort -> Expr -> Expr -> Expr
eAppC s e1 e2 = ECst (EApp e1 e2) s

--------------------------------------------------------------------------------
debruijnIndex :: Expr -> Int
debruijnIndex = go
  where
    go (ELam _ e)      = 1 + go e
    go (ECst e _)      = go e
    go (EApp e1 e2)    = go e1 + go e2
    go (ESym _)        = 1
    go (ECon _)        = 1
    go (EVar _)        = 1
    go (ENeg e)        = go e
    go (EBin _ e1 e2)  = go e1 + go e2
    go (EIte e e1 e2)  = go e + go e1 + go e2
    go (ETAbs e _)     = go e
    go (ETApp e _)     = go e
    go (PAnd es)       = foldl (\n e -> n + go e) 0 es
    go (POr es)        = foldl (\n e -> n + go e) 0 es
    go (PNot e)        = go e
    go (PImp e1 e2)    = go e1 + go e2
    go (PIff e1 e2)    = go e1 + go e2
    go (PAtom _ e1 e2) = go e1 + go e2
    go (PAll _ e)      = go e
    go (PExist _ e)    = go e
    go (PKVar _ _)     = 1
    go (PGrad _ _ _ e) = go e
    go (ECoerc _ _ e)  = go e

-- | Parsed refinement of @Symbol@ as @Expr@
--   e.g. in '{v: _ | e }' v is the @Symbol@ and e the @Expr@
newtype Reft = Reft (Symbol, Expr)
               deriving (Eq, Data, Typeable, Generic)

data SortedReft = RR { sr_sort :: !Sort, sr_reft :: !Reft }
                  deriving (Eq, Data, Typeable, Generic)

elit :: Located Symbol -> Sort -> Expr
elit l s = ECon $ L (symbolText $ val l) s

instance Fixpoint Constant where
  toFix (I i)   = toFix i
  toFix (R i)   = toFix i
  toFix (L s t) = parens $ text "lit" <+> text "\"" <-> toFix s <-> text "\"" <+> toFix t

--------------------------------------------------------------------------------
-- | String Constants ----------------------------------------------------------
--------------------------------------------------------------------------------

-- | Replace all symbol-representations-of-string-literals with string-literal
--   Used to transform parsed output from fixpoint back into fq.

instance Symbolic SymConst where
  symbol = encodeSymConst

encodeSymConst        :: SymConst -> Symbol
encodeSymConst (SL s) = litSymbol $ symbol s

-- _decodeSymConst :: Symbol -> Maybe SymConst
-- _decodeSymConst = fmap (SL . symbolText) . unLitSymbol

instance Fixpoint SymConst where
  toFix  = toFix . encodeSymConst

instance Fixpoint KVar where
  toFix (KV k) = text "$" <-> toFix k

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
  -- toFix (ECst e _so)   = toFix e
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
  toFix (PKVar k su)     = toFix k <-> toFix su
  toFix (PAll xts p)     = "forall" <+> (toFix xts
                                        $+$ ("." <+> toFix p))
  toFix (PExist xts p)   = "exists" <+> (toFix xts
                                        $+$ ("." <+> toFix p))
  toFix (ETApp e s)      = text "tapp" <+> toFix e <+> toFix s
  toFix (ETAbs e s)      = text "tabs" <+> toFix e <+> toFix s
  toFix (PGrad k _ _ e)  = toFix e <+> text "&&" <+> toFix k -- text "??" -- <+> toFix k <+> toFix su
  toFix (ECoerc a t e)   = parens (text "coerce" <+> toFix a <+> text "~" <+> toFix t <+> text "in" <+> toFix e)
  toFix (ELam (x,s) e)   = text "lam" <+> toFix x <+> ":" <+> toFix s <+> "." <+> toFix e

  simplify (PAnd [])     = PTrue
  simplify (POr  [])     = PFalse
  simplify (PAnd [p])    = simplify p
  simplify (POr  [p])    = simplify p

  simplify (PGrad k su i e)
    | isContraPred e      = PFalse
    | otherwise           = PGrad k su i (simplify e)

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

isEq  :: Brel -> Bool
isEq r          = r == Eq || r == Ueq

instance PPrint Constant where
  pprintTidy _ = toFix

instance PPrint Brel where
  pprintTidy _ Eq = "=="
  pprintTidy _ Ne = "/="
  pprintTidy _ r  = toFix r

instance PPrint Bop where
  pprintTidy _  = toFix

instance PPrint Sort where
  pprintTidy _ = toFix

instance PPrint a => PPrint (TCEmb a) where 
  pprintTidy k = pprintTidy k . tceToList 

instance PPrint KVar where
  pprintTidy _ (KV x) = text "$" <-> pprint x

instance PPrint SymConst where
  pprintTidy _ (SL x) = doubleQuotes $ text $ T.unpack x

-- | Wrap the enclosed 'Doc' in parentheses only if the condition holds.
parensIf :: Bool -> Doc -> Doc
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

opPrec :: Bop -> Int
opPrec Mod    = 5
opPrec Plus   = 6
opPrec Minus  = 6
opPrec Times  = 7
opPrec RTimes = 7
opPrec Div    = 7
opPrec RDiv   = 7

instance PPrint Expr where
  pprintPrec _ k (ESym c)        = pprintTidy k c
  pprintPrec _ k (ECon c)        = pprintTidy k c
  pprintPrec _ k (EVar s)        = pprintTidy k s
  -- pprintPrec _ (EBot)          = text "_|_"
  pprintPrec z k (ENeg e)        = parensIf (z > zn) $
                                   "-" <-> pprintPrec (zn + 1) k e
    where zn = 2
  pprintPrec z k (EApp f es)     = parensIf (z > za) $
                                   pprintPrec za k f <+> pprintPrec (za+1) k es
    where za = 8
  pprintPrec z k (EBin o e1 e2)  = parensIf (z > zo) $
                                   pprintPrec (zo+1) k e1 <+>
                                   pprintTidy k o         <+>
                                   pprintPrec (zo+1) k e2
    where zo = opPrec o
  pprintPrec z k (EIte p e1 e2)  = parensIf (z > zi) $
                                   "if"   <+> pprintPrec (zi+1) k p  <+>
                                   "then" <+> pprintPrec (zi+1) k e1 <+>
                                   "else" <+> pprintPrec (zi+1) k e2
    where zi = 1

  -- RJ: DO NOT DELETE!
  --  pprintPrec _ k (ECst e so)     = parens $ pprint e <+> ":" <+> {- const (text "...") -} (pprintTidy k so)
  pprintPrec z k (ECst e _)      = pprintPrec z k e
  pprintPrec _ _ PTrue           = trueD
  pprintPrec _ _ PFalse          = falseD
  pprintPrec z k (PNot p)        = parensIf (z > zn) $
                                   "not" <+> pprintPrec (zn+1) k p
    where zn = 8
  pprintPrec z k (PImp p1 p2)    = parensIf (z > zi) $
                                   (pprintPrec (zi+1) k p1) <+>
                                   "=>"                     <+>
                                   (pprintPrec (zi+1) k p2)
    where zi = 2
  pprintPrec z k (PIff p1 p2)    = parensIf (z > zi) $
                                   (pprintPrec (zi+1) k p1) <+>
                                   "<=>"                    <+>
                                   (pprintPrec (zi+1) k p2)
    where zi = 2
  pprintPrec z k (PAnd ps)       = parensIf (z > za) $
                                   pprintBin (za + 1) k trueD andD ps
    where za = 3
  pprintPrec z k (POr  ps)       = parensIf (z > zo) $
                                   pprintBin (zo + 1) k falseD orD ps
    where zo = 3
  pprintPrec z k (PAtom r e1 e2) = parensIf (z > za) $
                                   pprintPrec (za+1) k e1 <+>
                                   pprintTidy k r         <+>
                                   pprintPrec (za+1) k e2
    where za = 4
  pprintPrec _ k (PAll xts p)    = pprintQuant k "forall" xts p
  pprintPrec _ k (PExist xts p)  = pprintQuant k "exists" xts p
  pprintPrec _ k (ELam (x,t) e)  = "lam" <+> toFix x <+> ":" <+> toFix t <+> text "." <+> pprintTidy k e
  pprintPrec _ k (ECoerc a t e)  = parens $ "coerce" <+> toFix a <+> "~" <+> toFix t <+> text "in" <+> pprintTidy k e
  pprintPrec _ _ p@(PKVar {})    = toFix p
  pprintPrec _ _ (ETApp e s)     = "ETApp" <+> toFix e <+> toFix s
  pprintPrec _ _ (ETAbs e s)     = "ETAbs" <+> toFix e <+> toFix s
  pprintPrec z k (PGrad x _ _ e) = pprintPrec z k e <+> "&&" <+> toFix x -- "??"

pprintQuant :: Tidy -> Doc -> [(Symbol, Sort)] -> Expr -> Doc
pprintQuant k d xts p = (d <+> toFix xts)
                        $+$
                        ("  ." <+> pprintTidy k p)

trueD, falseD, andD, orD :: Doc
trueD  = "true"
falseD = "false"
andD   = "&&"
orD    = "||"

pprintBin :: (PPrint a) => Int -> Tidy -> Doc -> Doc -> [a] -> Doc
pprintBin _ _ b _ [] = b
pprintBin z k _ o xs = vIntersperse o $ pprintPrec z k <$> xs

vIntersperse :: Doc -> [Doc] -> Doc
vIntersperse _ []     = empty
vIntersperse _ [d]    = d
vIntersperse s (d:ds) = vcat (d : ((s <+>) <$> ds))

pprintReft :: Tidy -> Reft -> Doc
pprintReft k (Reft (_,ra)) = pprintBin z k trueD andD flat
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

instance Expression SortedReft where
  expr (RR _ r) = expr r

instance Expression Reft where
  expr (Reft(_, e)) = e

instance Expression Expr where
  expr = id

-- | The symbol may be an encoding of a SymConst.

instance Expression Symbol where
  expr s = eVar s

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
isSingletonExpr v (PIff e1 e2) 
  | e1 == EVar v           = Just e2
  | e2 == EVar v           = Just e1
isSingletonExpr _ _        = Nothing

pAnd, pOr     :: ListNE Pred -> Pred
pAnd          = simplify . PAnd
pOr           = simplify . POr

(&.&) :: Pred -> Pred -> Pred
(&.&) p q = pAnd [p, q]

(|.|) :: Pred -> Pred -> Pred
(|.|) p q = pOr [p, q]

pIte :: Pred -> Expr -> Expr -> Expr
pIte p1 p2 p3 = pAnd [p1 `PImp` p2, (PNot p1) `PImp` p3]

pExist :: [(Symbol, Sort)] -> Pred -> Pred
pExist []  p = p
pExist xts p = PExist xts p

mkProp :: Expr -> Pred
mkProp = id -- EApp (EVar propConName)

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
-- | Gradual Type Manipulation  ----------------------------
------------------------------------------------------------
pGAnds :: [Expr] -> Expr
pGAnds = foldl pGAnd PTrue

pGAnd :: Expr -> Expr -> Expr
pGAnd (PGrad k su i p) q = PGrad k su i (pAnd [p, q])
pGAnd p (PGrad k su i q) = PGrad k su i (pAnd [p, q])
pGAnd p q              = pAnd [p,q]

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
  syms   :: a -> [Symbol]                   -- ^ free symbols of a
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
