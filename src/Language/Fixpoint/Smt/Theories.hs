{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.Fixpoint.Smt.Theories where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import qualified Data.HashMap.Strict      as M
-- import qualified Data.List                as L
import qualified Data.Text                as T
import           Data.Text.Format
-- import           Data.Monoid


--import           Language.Fixpoint.Errors
--import           Language.Fixpoint.Files
import           Control.Applicative      ((<$>))
--import           Control.Monad
--import           Data.Char
--import qualified Data.Text.IO             as TIO
import qualified Data.Text.Lazy           as LT
--import qualified Data.Text.Lazy.IO        as LTIO
--import           System.Directory
--import           System.Exit              hiding (die)
--import           System.FilePath
--import           System.IO                (Handle, IOMode (..), hClose, hFlush, openFile)
--import           System.Process
--import qualified Data.Attoparsec.Text     as A



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


setEmp, setCap, setSub, setAdd, setMem, setCom, setCup, setDif, setSng :: Symbol
setEmp = "Set_emp"
setCap = "Set_cap"
setSub = "Set_sub"
setAdd = "Set_add"
setMem = "Set_mem"
setCom = "Set_com"
setCup = "Set_cup"
setDif = "Set_dif"
setSng = "Set_sng"

z3Preamble :: [LT.Text]
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
    ]

smtlibPreamble :: [LT.Text]
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
  ]

tSym :: Symbol -> Raw -> Sort -> (Symbol, TheorySymbol)
tSym x n t = (x, Thy x n t)

smt2Theory :: Symbol -> Maybe T.Text
smt2Theory x = tsRaw <$> M.lookup x theorySymbols
