{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

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

     ) where

import           Prelude hiding (map)
import           Language.Fixpoint.Config
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import qualified Data.HashMap.Strict      as M
import qualified Data.Text                as T
import           Data.Text.Format         hiding (format)


--------------------------------------------------------------------------
-- | Set Theory ----------------------------------------------------------
--------------------------------------------------------------------------

elt, set, map, bit, sz32, sz64 :: Raw
elt  = "Elt"
set  = "Set"
map  = "Map"
bit  = "BitVec"
sz32 = "Size32"
sz64 = "Size64"


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

z3Preamble :: [T.Text]
z3Preamble
  = [ format "(define-sort {} () Int)"
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
    ]

smtlibPreamble :: [T.Text]
smtlibPreamble
  = [        "(set-logic QF_UFLIA)"
    , format "(define-sort {} () Int)"       (Only elt)
    , format "(define-sort {} () Int)"       (Only set)
    , format "(declare-fun {} () {})"        (emp, set)
    , format "(declare-fun {} ({} {}) {})"   (add, set, elt, set)
    , format "(declare-fun {} ({} {}) {})"   (cup, set, set, set)
    , format "(declare-fun {} ({} {}) {})"   (cap, set, set, set)
    , format "(declare-fun {} ({} {}) {})"   (dif, set, set, set)
    , format "(declare-fun {} ({} {}) Bool)" (sub, set, set)
    , format "(declare-fun {} ({} {}) Bool)" (mem, elt, set)
    , format "(declare-fun {} ({} {}) {})"    (sel, map, elt, elt)
    , format "(declare-fun {} ({} {} {}) {})" (sto, map, elt, elt, map)
    ]

mkSetSort _ _  = set
mkEmptySet _ _ = emp
mkSetAdd _ s x = format "({} {} {})" (add, s, x)
mkSetMem _ x s = format "({} {} {})" (mem, x, s)
mkSetCup _ s t = format "({} {} {})" (cup, s, t)
mkSetCap _ s t = format "({} {} {})" (cap, s, t)
mkSetDif _ s t = format "({} {} {})" (dif, s, t)
mkSetSub _ s t = format "({} {} {})" (sub, s, t)


-- smt_set_funs :: M.HashMap Symbol Raw
-- smt_set_funs = M.fromList [ (setEmp, emp), (setAdd, add), (setCup, cup)
--                           , (setCap, cap), (setMem, mem), (setDif, dif)
--                           , (setSub, sub), (setCom, com)]

theorySymbols :: M.HashMap Symbol TheorySymbol
theorySymbols = M.fromList
  [ tSym setEmp emp undefined
  , tSym setAdd add undefined
  , tSym setCup cup undefined
  , tSym setCap cap undefined
  , tSym setMem mem undefined
  , tSym setDif dif undefined
  , tSym setSub sub undefined
  , tSym setCom com undefined
  , tSym mapSel sel undefined
  , tSym mapSto sto undefined
  ]

tSym :: Symbol -> Raw -> Sort -> (Symbol, TheorySymbol)
tSym x n t = (x, Thy x n t)

-------------------------------------------------------------------------------
-- | Exported API -------------------------------------------------------------
-------------------------------------------------------------------------------

smt2Symbol :: Symbol -> Maybe T.Text
smt2Symbol x = tsRaw <$> M.lookup x theorySymbols

smt2Sort :: Sort -> Maybe T.Text
smt2Sort (FApp (FTC c) t)
  | fTyconSymbol c == "Set_Set" = Just $ format "{}" (Only set)
smt2Sort (FApp (FApp (FTC c) t1) t2)
  | fTyconSymbol c == "Map_t"   = Just $ format "{}" (Only map)
smt2Sort _                      = Nothing

smt2App :: LocSymbol -> [T.Text] -> Maybe T.Text
smt2App f [d]
  | val f == setEmpty = Just $ format "{}"             (Only emp)
  | val f == setEmp   = Just $ format "(= {} {})"      (emp, d)
  | val f == setSng   = Just $ format "({} {} {})"     (add, emp, d)
smt2App _ _           = Nothing

preamble :: SMTSolver -> [T.Text]
preamble Z3 = z3Preamble
preamble _  = smtlibPreamble
