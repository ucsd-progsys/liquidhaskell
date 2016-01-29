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

     ) where

import           Prelude hiding (map)
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import qualified Data.HashMap.Strict      as M
import qualified Data.Text                as T
import           Data.Text.Format         hiding (format)


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

z3Preamble :: Bool -> [T.Text]
z3Preamble u
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
    , uifDef u (symbolText mulFuncName) ("*"::T.Text)
    , uifDef u (symbolText divFuncName) ("/"::T.Text)
    ]

uifDef u f op | u         = format "(declare-fun {} (Real Real) Real)" (Only f)
              | otherwise = format "(define-fun {} ((x Real) (y Real)) Real ({} x y))" (f, op)

smtlibPreamble :: Bool -> [T.Text]
smtlibPreamble _ --TODO use uif flag u (see z3Preamble)
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
  , tSym bvOrName "bvor" undefined 
  , tSym bvAndName "bvand" undefined 
  ]

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

smt2Symbol :: Symbol -> Maybe T.Text
smt2Symbol x = tsRaw <$> M.lookup x theorySymbols

smt2Sort :: Sort -> Maybe T.Text
smt2Sort (FApp (FTC c) _)
  | fTyconSymbol c == "Set_Set" = Just $ format "{}" (Only set)
smt2Sort (FApp (FApp (FTC c) _) _)
  | fTyconSymbol c == "Map_t"   = Just $ format "{}" (Only map)
smt2Sort (FApp (FTC bv) (FTC s))
  | isBv bv
  , Just n <- sizeBv s          = Just $ format "(_ BitVec {})" (Only n)
smt2Sort _                      = Nothing

smt2App :: Expr -> [T.Text] -> Maybe T.Text
smt2App (EVar f) [d]
  | f == setEmpty = Just $ format "{}"             (Only emp)
  | f == setEmp   = Just $ format "(= {} {})"      (emp, d)
  | f == setSng   = Just $ format "({} {} {})"     (add, emp, d)
smt2App (EVar f) ds
  | Just s <- M.lookup f theorySymbols
  = Just $ format "({} {})" (tsRaw s, T.intercalate " " ds) 
smt2App _ _           = Nothing


preamble :: Bool -> SMTSolver -> [T.Text]
preamble u Z3 = z3Preamble u
preamble u _  = smtlibPreamble u
