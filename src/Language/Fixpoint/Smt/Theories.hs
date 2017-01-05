{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE PatternGuards             #-}

module Language.Fixpoint.Smt.Theories
     (
       -- * Convert theory applications TODO: merge with smt2symbol
       smt2App
       -- * Convert theory sorts
     , smt2Sort
       -- * Convert theory symbols
     , smt2Symbol
       -- * Preamble to initialize SMT
     , preamble

       -- * Bit Vector Operations
     , sizeBv
     , toInt

       -- * Theory Symbols
     , theorySymbols
     , theorySEnv

     -- * String
     -- , string
     -- , genLen

       -- * Theories
     , setEmpty, setEmp, setCap, setSub, setAdd, setMem
     , setCom, setCup, setDif, setSng, mapSel, mapSto

      -- * Query Theories
     , isSmt2App
     , isConName
     , axiomLiterals
     ) where

import           Prelude hiding (map)
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import qualified Data.HashMap.Strict      as M
import           Data.Maybe (catMaybes, isJust)
import           Data.Monoid
import qualified Data.Text.Lazy           as T
import qualified Data.Text.Lazy.Builder   as Builder
import           Data.Text.Format
import qualified Data.Text
import           Data.String                 (IsString(..))

--------------------------------------------------------------------------
-- | Set Theory ----------------------------------------------------------
--------------------------------------------------------------------------

elt, set, map :: Raw
elt  = "Elt"
set  = "Set"
map  = "Map"

emp, add, cup, cap, mem, dif, sub, com, sel, sto :: Raw
emp   = "smt_set_emp"
add   = "smt_set_add"
cup   = "smt_set_cup"
cap   = "smt_set_cap"
mem   = "smt_set_mem"
dif   = "smt_set_dif"
sub   = "smt_set_sub"
com   = "smt_set_com"
sel   = "smt_map_sel"
sto   = "smt_map_sto"

setEmpty, setEmp, setCap, setSub, setAdd, setMem, setCom, setCup, setDif, setSng, mapSel, mapSto :: Symbol
setEmpty = "Set_empty"
setEmp   = "Set_emp"
setCap   = "Set_cap"
setSub   = "Set_sub"
setAdd   = "Set_add"
setMem   = "Set_mem"
setCom   = "Set_com"
setCup   = "Set_cup"
setDif   = "Set_dif"
setSng   = "Set_sng"
mapSel   = "Map_select"
mapSto   = "Map_store"


strLen, strSubstr, strConcat :: (IsString a) => a -- Symbol
strLen    = "strLen"
strSubstr = "subString"
strConcat = "concatString"
-- NOPROP genLen :: Symbol
-- NOPROP genLen = "len"

-- NOPROP strlen, strsubstr, strconcat :: Raw
-- NOPROP strlen    = "strLen"
-- NOPROP strsubstr = "subString"
-- NOPROP strconcat = "concatString"

z3strlen, z3strsubstr, z3strconcat :: Raw
z3strlen    = "str.len"
z3strsubstr = "str.substr"
z3strconcat = "str.++"

strLenSort, substrSort, concatstrSort :: Sort
strLenSort    = FFunc strSort intSort
substrSort    = mkFFunc 0 [strSort, intSort, intSort, strSort]
concatstrSort = mkFFunc 0 [strSort, strSort, strSort]

string :: Raw
string = strConName

z3Preamble :: Config -> [T.Text]
z3Preamble u
  = stringPreamble u ++
    [ format "(define-sort {} () Int)"
        (Only elt)
    , format "(define-sort {} () (Array {} Bool))"
        (set, elt)
    , format "(define-fun {} () {} ((as const {}) false))"
        (emp, set, set)
    , format "(define-fun {} ((x {}) (s {})) Bool (select s x))"
        (mem, elt, set)
    , format "(define-fun {} ((s {}) (x {})) {} (store s x true))"
        (add, set, elt, set)
    , format "(define-fun {} ((s1 {}) (s2 {})) {} ((_ map or) s1 s2))"
        (cup, set, set, set)
    , format "(define-fun {} ((s1 {}) (s2 {})) {} ((_ map and) s1 s2))"
        (cap, set, set, set)
    , format "(define-fun {} ((s {})) {} ((_ map not) s))"
        (com, set, set)
    , format "(define-fun {} ((s1 {}) (s2 {})) {} ({} s1 ({} s2)))"
        (dif, set, set, set, cap, com)
    , format "(define-fun {} ((s1 {}) (s2 {})) Bool (= {} ({} s1 s2)))"
        (sub, set, set, emp, dif)
    , format "(define-sort {} () (Array {} {}))"
        (map, elt, elt)
    , format "(define-fun {} ((m {}) (k {})) {} (select m k))"
        (sel, map, elt, elt)
    , format "(define-fun {} ((m {}) (k {}) (v {})) {} (store m k v))"
        (sto, map, elt, elt, map)
    , format "(define-fun {} ((b Bool)) Int (ite b 1 0))"
        (Only (boolToIntName :: T.Text))
    , uifDef u (symbolText mulFuncName) ("*"   :: T.Text)
    , uifDef u (symbolText divFuncName) "div"
    ]

-- RJ: Am changing this to `Int` not `Real` as (1) we usually want `Int` and
-- (2) have very different semantics. TODO: proper overloading, post genEApp
uifDef :: Config -> Data.Text.Text -> T.Text -> T.Text
uifDef cfg f op
  | linear cfg || Z3 /= solver cfg
  = format "(declare-fun {} (Int Int) Int)" (Only f)
  | otherwise
  = format "(define-fun {} ((x Int) (y Int)) Int ({} x y))" (f, op)

cvc4Preamble :: Config -> [T.Text]
cvc4Preamble _ --TODO use uif flag u (see z3Preamble)
  = [        "(set-logic ALL_SUPPORTED)"
    , format "(define-sort {} () Int)"       (Only elt)
    , format "(define-sort {} () Int)"       (Only set)
    , format "(define-sort {} () Int)"       (Only string)
    , format "(declare-fun {} () {})"        (emp, set)
    , format "(declare-fun {} ({} {}) {})"   (add, set, elt, set)
    , format "(declare-fun {} ({} {}) {})"   (cup, set, set, set)
    , format "(declare-fun {} ({} {}) {})"   (cap, set, set, set)
    , format "(declare-fun {} ({} {}) {})"   (dif, set, set, set)
    , format "(declare-fun {} ({} {}) Bool)" (sub, set, set)
    , format "(declare-fun {} ({} {}) Bool)" (mem, elt, set)
    , format "(define-sort {} () (Array {} {}))"
        (map, elt, elt)
    , format "(define-fun {} ((m {}) (k {})) {} (select m k))"
        (sel, map, elt, elt)
    , format "(define-fun {} ((m {}) (k {}) (v {})) {} (store m k v))"
        (sto, map, elt, elt, map)
    , format "(define-fun {} ((b Bool)) Int (ite b 1 0))"
        (Only (boolToIntName :: Raw))
    ]

smtlibPreamble :: Config -> [T.Text]
smtlibPreamble _ --TODO use uif flag u (see z3Preamble)
  = [       --  "(set-logic QF_AUFRIA)",
      format "(define-sort {} () Int)"       (Only elt)
    , format "(define-sort {} () Int)"       (Only set)
    , format "(declare-fun {} () {})"        (emp, set)
    , format "(declare-fun {} ({} {}) {})"   (add, set, elt, set)
    , format "(declare-fun {} ({} {}) {})"   (cup, set, set, set)
    , format "(declare-fun {} ({} {}) {})"   (cap, set, set, set)
    , format "(declare-fun {} ({} {}) {})"   (dif, set, set, set)
    , format "(declare-fun {} ({} {}) Bool)" (sub, set, set)
    , format "(declare-fun {} ({} {}) Bool)" (mem, elt, set)
    , format "(define-sort {} () Int)"       (Only map)
    , format "(declare-fun {} ({} {}) {})"    (sel, map, elt, elt)
    , format "(declare-fun {} ({} {} {}) {})" (sto, map, elt, elt, map)
    , format "(declare-fun {} ({} {} {}) {})" (sto, map, elt, elt, map)
    , format "(define-fun {} ((b Bool)) Int (ite b 1 0))" (Only (boolToIntName :: Raw))
    ]


stringPreamble :: Config -> [T.Text]
stringPreamble cfg | stringTheory cfg
  = [
      format "(define-sort {} () String)" (Only string)
    , format "(define-fun {} ((s {})) Int ({} s))"
        (strLen :: Raw, string, z3strlen)
    , format "(define-fun {} ((s {}) (i Int) (j Int)) {} ({} s i j))"
        (strSubstr :: Raw, string, string, z3strsubstr)
    , format "(define-fun {} ((x {}) (y {})) {} ({} x y))"
        (strConcat :: Raw, string, string, string, z3strconcat)
    ]
stringPreamble _
  = [
      format "(define-sort {} () Int)" (Only string)
    , format "(declare-fun {} ({}) Int)"
        (strLen :: Raw, string)
    , format "(declare-fun {} ({} Int Int) {})"
        (strSubstr :: Raw, string, string)
    , format "(declare-fun {} ({} {}) {})"
        (strConcat :: Raw, string, string, string)
    ]



-------------------------------------------------------------------------------
-- | Exported API -------------------------------------------------------------
-------------------------------------------------------------------------------
smt2Symbol :: Symbol -> Maybe Builder.Builder
smt2Symbol x = Builder.fromLazyText . tsRaw <$> M.lookup x theorySymbols

smt2Sort :: Sort -> Maybe Builder.Builder
smt2Sort (FApp (FTC c) _)
  | isConName setConName c      = Just $ build "{}" (Only set)
smt2Sort (FApp (FApp (FTC c) _) _)
  | isConName mapConName c      = Just $ build "{}" (Only map)
smt2Sort (FApp (FTC bv) (FTC s))
  | isConName bitVecName bv
  , Just n <- sizeBv s          = Just $ build "(_ BitVec {})" (Only n)
smt2Sort s
  | isString s                  = Just $ build "{}" (Only string)
smt2Sort _                      = Nothing

smt2App :: Expr -> [Builder.Builder] -> Maybe Builder.Builder
smt2App (EVar f) [d]
  | f == setEmpty = Just $ build "{}"             (Only emp)
  | f == setEmp   = Just $ build "(= {} {})"      (emp, d)
  | f == setSng   = Just $ build "({} {} {})"     (add, emp, d)
smt2App (EVar f) (d:ds)
  | Just s <- M.lookup f theorySymbols
  = Just $ build "({} {})" (tsRaw s, d <> mconcat [ " " <> d | d <- ds])
smt2App _ _           = Nothing

-- isSmt2App :: Expr -> [a] -> Bool
-- isSmt2App e xs = tracepp ("isSmt2App e := " ++ show e) (isSmt2App' e xs)

isSmt2App :: Expr -> [a] -> Bool
isSmt2App (EVar f) [_]
  | f == setEmpty = True
  | f == setEmp   = True
  | f == setSng   = True
isSmt2App (EVar f) _
  =  isJust $ M.lookup f theorySymbols
isSmt2App _ _
  = False


preamble :: Config -> SMTSolver -> [T.Text]
preamble u Z3   = z3Preamble u
preamble u Cvc4 = cvc4Preamble u
preamble u _    = smtlibPreamble u

--------------------------------------------------------------------------------
-- | Converting Non-Int types to Int -------------------------------------------
--------------------------------------------------------------------------------
-- toInt :: Expr -> Sort -> Expr
-- toInt e s = tracepp msg (toInt' e s)
  -- where
    -- msg   = "toInt e = " ++ show e ++ ", t = " ++ show s

toInt :: Expr -> Sort -> Expr
toInt e s
  |  (FApp (FTC c) _) <- s
  , isConName setConName c
  = castWith setToIntName e
  | (FApp (FApp (FTC c) _) _) <- s
  , isConName mapConName c
  = castWith mapToIntName e
  | (FApp (FTC bv) (FTC s)) <- s
  , isConName bitVecName bv
  , Just _ <- sizeBv s
  = castWith bitVecToIntName e
  | FTC c <- s
  , c == boolFTyCon
  = castWith boolToIntName e
  | FTC c <- s
  , c == realFTyCon
  = castWith realToIntName e
  | otherwise
  = e

castWith :: Symbol -> Expr -> Expr
castWith s = eAppC intSort (EVar s)

--------------------------------------------------------------------------------
-- | Theory Symbols : `uninterpSEnv` should be disjoint from see `interpSEnv`
--   to avoid duplicate SMT definitions.  `uninterpSEnv` is for uninterpreted
--   symbols, and `interpSEnv` is for interpreted symbols.
--------------------------------------------------------------------------------
theorySEnv :: SEnv Sort
theorySEnv = fromListSEnv . M.toList . fmap tsSort $ theorySymbols

-- | `theorySymbols` contains the list of ALL SMT symbols with interpretations,
--   i.e. which are given via `define-fun` (as opposed to `declare-fun`)
theorySymbols :: M.HashMap Symbol TheorySymbol
theorySymbols = M.fromList $ uninterpSymbols ++ interpSymbols

-- isTheorySymbol :: Symbol -> Bool
-- isTheorySymbol x = M.member x theorySymbols

interpSymbols :: [(Symbol, TheorySymbol)]
interpSymbols =
  [ interpSym setEmp   emp  (FAbs 0 $ FFunc (setSort $ FVar 0) boolSort)
  , interpSym setEmpty emp  (FAbs 0 $ FFunc intSort (setSort $ FVar 0))
  , interpSym setAdd   add   setBopSort
  , interpSym setCup   cup   setBopSort
  , interpSym setCap   cap   setBopSort
  , interpSym setMem   mem   setMemSort
  , interpSym setDif   dif   setBopSort
  , interpSym setSub   sub   setCmpSort
  , interpSym setCom   com   setCmpSort
  , interpSym mapSel   sel   mapSelSort
  , interpSym mapSto   sto   mapStoSort
  , interpSym bvOrName "bvor"   bvBopSort
  , interpSym bvAndName "bvand" bvBopSort
  , interpSym strLen    strLen    strLenSort
  , interpSym strSubstr strSubstr substrSort
  , interpSym strConcat strConcat concatstrSort
  , interpSym boolInt   boolInt   (FFunc boolSort intSort)
  ]
  where
    boolInt    = boolToIntName
    setBopSort = FAbs 0 $ FFunc (setSort $ FVar 0) $ FFunc (setSort $ FVar 0) (setSort $ FVar 0)
    setMemSort = FAbs 0 $ FFunc (FVar 0) $ FFunc (setSort $ FVar 0) boolSort
    setCmpSort = FAbs 0 $ FFunc (setSort $ FVar 0) $ FFunc (setSort $ FVar 0) boolSort
    mapSelSort = FAbs 0 $ FAbs 1 $ FFunc (mapSort (FVar 0) (FVar 1)) $ FFunc (FVar 0) (FVar 1)
    mapStoSort = FAbs 0 $ FAbs 1 $ FFunc (mapSort (FVar 0) (FVar 1))
                                 $ FFunc (FVar 0)
                                 $ FFunc (FVar 1)
                                         (mapSort (FVar 0) (FVar 1))
    bvBopSort  = FFunc bitVecSort $ FFunc bitVecSort bitVecSort


interpSym :: Symbol -> Raw -> Sort -> (Symbol, TheorySymbol)
interpSym x n t = (x, Thy x n t True)

isConName :: Symbol -> FTycon -> Bool
isConName s = (s ==) . val . fTyconSymbol

sizeBv :: FTycon -> Maybe Int
sizeBv tc
  | s == size32Name = Just 32
  | s == size64Name = Just 64
  | otherwise       = Nothing
  where
    s               = val $ fTyconSymbol tc

uninterpSymbols :: [(Symbol, TheorySymbol)]
uninterpSymbols = [ (x, uninterpSym x t) | (x, t) <- uninterpSymbols']

uninterpSym :: Symbol -> Sort -> TheorySymbol
uninterpSym x t =  Thy x (lt x) t False
  where
    lt           = T.fromStrict . symbolSafeText

uninterpSymbols' :: [(Symbol, Sort)]
uninterpSymbols' =
  [ (setToIntName,    FFunc (setSort intSort)   intSort)
  , (bitVecToIntName, FFunc bitVecSort intSort)
  , (mapToIntName,    FFunc (mapSort intSort intSort) intSort)
  , (realToIntName,   FFunc realSort   intSort)
  , (lambdaName   ,   FFunc intSort (FFunc intSort intSort))
  ]
  ++ concatMap makeApplies [1..maxLamArg]
  ++ [(makeLamArg s i, s) | i <- [1..maxLamArg], s <- sorts]

-- THESE ARE DUPLICATED IN DEFUNCTIONALIZATION
maxLamArg :: Int
maxLamArg = 7

sorts :: [Sort]
sorts = [intSort]

-- NIKI TODO: allow non integer lambda arguments
-- sorts = [setSort intSort, bitVecSort intSort, mapSort intSort intSort, boolSort, realSort, intSort]

makeLamArg :: Sort -> Int  -> Symbol
makeLamArg _ = intArgName

makeApplies :: Int -> [(Symbol, Sort)]
makeApplies i =
  [ (intApplyName i,    go i intSort)
  , (setApplyName i,    go i (setSort intSort))
  , (bitVecApplyName i, go i bitVecSort)
  , (mapApplyName i,    go i $ mapSort intSort intSort)
  , (realApplyName i,   go i realSort)
  , (boolApplyName i,   go i boolSort)
  ]
  where
    go 0 s = FFunc intSort s
    go i s = FFunc intSort $ go (i-1) s

axiomLiterals :: [(Symbol, Sort)] -> [Expr]
axiomLiterals lts = catMaybes [ lenAxiom l <$> litLen l | (l, t) <- lts, isString t ]
  where
    lenAxiom l n  = EEq (EApp (expr (strLen :: Symbol)) (expr l)) (expr n `ECst` intSort)
    litLen        = fmap (Data.Text.length .  symbolText) . unLitSymbol
