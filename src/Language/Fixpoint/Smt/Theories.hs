
--------------------------------------------------------------------------
-- | Set Theory ----------------------------------------------------------
--------------------------------------------------------------------------

elt, set :: Raw
elt  = "Elt"
set  = "Set"
map  = "Map"
bit  = "BitVec"
sz32 = "Size32"
sz64 = "Size64"


emp, add, cup, cap, mem, dif, sub, com :: Raw
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

setEmp = "Set_emp"  :: Symbol
setCap = "Set_cap"  :: Symbol
setSub = "Set_sub"  :: Symbol
setAdd = "Set_add"  :: Symbol
setMem = "Set_mem"  :: Symbol
setCom = "Set_com"  :: Symbol
setCup = "Set_cup"  :: Symbol
setDif = "Set_dif"  :: Symbol
setSng = "Set_sng"  :: Symbol

smt_set_funs :: M.HashMap Symbol Raw
smt_set_funs = M.fromList [ (setEmp, emp), (setAdd, add), (setCup, cup)
                          , (setCap, cap), (setMem, mem), (setDif, dif)
                          , (setSub, sub), (setCom, com)]



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

