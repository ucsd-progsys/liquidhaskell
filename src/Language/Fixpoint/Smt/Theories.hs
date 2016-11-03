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
     , isBv, sizeBv

     , isTheorySymbol
     , theoryEnv

       -- * String
     , string
     , strLen, genLen

       -- * Theories
     , theorySymbols
     , setEmpty, setEmp, setCap, setSub, setAdd, setMem
     , setCom, setCup, setDif, setSng, mapSel, mapSto

      -- * Query Theories
     , isSmt2App
     ) where

import           Prelude hiding (map)
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import qualified Data.HashMap.Strict      as M
import Data.Maybe (isJust)
import Data.Monoid
import qualified Data.Text.Lazy           as T
import qualified Data.Text.Lazy.Builder   as Builder
import           Data.Text.Format
import qualified Data.Text

--------------------------------------------------------------------------
-- | Set Theory ----------------------------------------------------------
--------------------------------------------------------------------------

elt, set, map :: Raw
elt  = "Elt"
set  = "Set"
map  = "Map"


-- bit, sz32, sz64 :: Raw
-- bit  = symbolText bitVecName -- "BitVec"
-- sz32 = symbolText size32Name -- "Size32"
-- sz64 = symbolText size64Name -- "Size64"


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


strLen, strSubstr, genLen, strConcat :: Symbol
strLen    = "stringLen"
strSubstr = "subString"
strConcat = "concatString"

genLen = "len"


strlen, strsubstr, strconcat :: Raw
strlen    = "stringLen"
strsubstr = "subString"
strconcat = "concatString"


z3strlen, z3strsubstr, z3strconcat :: Raw
z3strlen    = "str.len"
z3strsubstr = "str.substr"
z3strconcat = "str.++"

strLenSort, substrSort, concatstrSort :: Sort
strLenSort    = FFunc strSort intSort
substrSort    = mkFFunc 0 [strSort, intSort, intSort, strSort]
concatstrSort = mkFFunc 0 [strSort, strSort, strSort]

string :: Raw
string = "Str"

z3Preamble :: Config -> [T.Text]
z3Preamble u
  = stringPrealble u ++
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
    , uifDef u (symbolText mulFuncName) ("*"::T.Text)
    , uifDef u (symbolText divFuncName) ("div"::T.Text)
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
    ]


stringPrealble :: Config -> [T.Text]
stringPrealble cfg | stringTheory cfg
  = [
      format "(define-sort {} () String)" (Only string)
    , format "(define-fun {} ((s {})) Int ({} s))"
        (strlen, string, z3strlen)
    , format "(define-fun {} ((s {}) (i Int) (j Int)) {} ({} s i j))"
        (strsubstr, string, string, z3strsubstr)
    , format "(define-fun {} ((x {}) (y {})) {} ({} x y))"
        (strconcat, string, string, string, z3strconcat)
    ]
stringPrealble _
  = [
      format "(define-sort {} () Int)" (Only string)
    , format "(declare-fun {} ({}) Int)"
        (strlen, string)
    , format "(declare-fun {} ({} Int Int) {})"
        (strsubstr, string, string)
    , format "(declare-fun {} ({} {}) {})"
        (strconcat, string, string, string)
    ]




{-
mkSetSort _ _  = set
mkEmptySet _ _ = emp
mkSetAdd _ s x = format "({} {} {})" (add, s, x)
mkSetMem _ x s = format "({} {} {})" (mem, x, s)
mkSetCup _ s t = format "({} {} {})" (cup, s, t)
mkSetCap _ s t = format "({} {} {})" (cap, s, t)
mkSetDif _ s t = format "({} {} {})" (dif, s, t)
mkSetSub _ s t = format "({} {} {})" (sub, s, t)
-}

-- smt_set_funs :: M.HashMap Symbol Raw
-- smt_set_funs = M.fromList [ (setEmp, emp), (setAdd, add), (setCup, cup)
--                           , (setCap, cap), (setMem, mem), (setDif, dif)
--                           , (setSub, sub), (setCom, com)]


isTheorySymbol :: Symbol -> Bool
isTheorySymbol x = M.member x theorySymbols

theoryEnv :: M.HashMap Symbol Sort
theoryEnv = M.map tsSort theorySymbols

theorySymbols :: M.HashMap Symbol TheorySymbol
theorySymbols = M.fromList
  [ tSym setEmp   emp (FAbs 0 $ FFunc (setSort $ FVar 0) boolSort)
  , tSym setEmpty emp (FAbs 0 $ FFunc intSort (setSort $ FVar 0))
  , tSym setAdd add   setBopSort
  , tSym setCup cup   setBopSort
  , tSym setCap cap   setBopSort
  , tSym setMem mem   setMemSort
  , tSym setDif dif   setBopSort
  , tSym setSub sub   setCmpSort
  , tSym setCom com   setCmpSort
  , tSym mapSel sel   mapSelSort
  , tSym mapSto sto   mapStoSort
  , tSym bvOrName "bvor"   bvBopSort
  , tSym bvAndName "bvand" bvBopSort

  , tSym strLen    strlen    strLenSort
  , tSym strSubstr strsubstr substrSort
  , tSym strConcat strconcat concatstrSort
  ]
  where
    setBopSort = FAbs 0 $ FFunc (setSort $ FVar 0) $ FFunc (setSort $ FVar 0) (setSort $ FVar 0)
    setMemSort = FAbs 0 $ FFunc (FVar 0) $ FFunc (setSort $ FVar 0) boolSort
    setCmpSort = FAbs 0 $ FFunc (setSort $ FVar 0) $ FFunc (setSort $ FVar 0) boolSort
    mapSelSort = FAbs 0 $ FAbs 1 $ FFunc (mapSort (FVar 0) (FVar 1)) $ FFunc (FVar 0) (FVar 1)
    mapStoSort = FAbs 0 $ FAbs 1 $ FFunc (mapSort (FVar 0) (FVar 1))
                                 $ FFunc (FVar 0)
                                 $ FFunc (FVar 1)
                                         (mapSort (FVar 0) (FVar 1))
    bvBopSort  = FFunc bitVecSort $ FFunc bitVecSort bitVecSort


tSym :: Symbol -> Raw -> Sort -> (Symbol, TheorySymbol)
tSym x n t = (x, Thy x n t)


isBv :: FTycon -> Bool
isBv = (bitVecName ==) . val . fTyconSymbol

sizeBv :: FTycon -> Maybe Int
sizeBv tc
  | s == size32Name = Just 32
  | s == size64Name = Just 64
  | otherwise       = Nothing
  where
    s               = val $ fTyconSymbol tc


-------------------------------------------------------------------------------
-- | Exported API -------------------------------------------------------------
-------------------------------------------------------------------------------

smt2Symbol :: Symbol -> Maybe Builder.Builder
smt2Symbol x = Builder.fromLazyText . tsRaw <$> M.lookup x theorySymbols

smt2Sort :: Sort -> Maybe Builder.Builder
smt2Sort (FApp (FTC c) _)
  | fTyconSymbol c == "Set_Set" = Just $ build "{}" (Only set)
smt2Sort (FApp (FApp (FTC c) _) _)
  | fTyconSymbol c == "Map_t"   = Just $ build "{}" (Only map)
smt2Sort (FApp (FTC bv) (FTC s))
  | isBv bv
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
