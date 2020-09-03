-- | This tests that we dig up sorts (for `applySorts`) from the BODIES of reflected functions.
-- c.f. https://piazza.com/class/jqk23zupq7a62c?cid=72

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}  -- Bug goes away if this line is commented
{-@ LIQUID "--short-names" @-}

module Test where

import Prelude hiding ((++), const, sum, init)

data GState k v = Init v | Bind k v (GState k v) 

type Proof = ()

{-@ reflect init @-}
init :: v -> GState k v
init v = Init v  

{-@ reflect set @-}
set :: GState k v -> k -> v -> GState k v
set s k v = Bind k v s 

{-@ reflect get @-}
get :: (Eq k) => GState k v -> k -> v
get (Init v)     _   = v
get (Bind k v s) key = if key == k then v else get s key

------------------------------------------------------------------------------
-- | Arithmetic Expressions
------------------------------------------------------------------------------

type Vname = String

data AExp
  = N Val
  | V Vname
  | Plus AExp AExp
  deriving (Show)

type Val   = Int
type State = GState Vname Val

{-@ reflect aval @-}
aval                :: AExp -> State -> Val
aval (N n) _        = n
aval (V x) s        = get s x
aval (Plus e1 e2) s = aval e1 s + aval e2 s

data LExp
  = LN    Int                 -- ^ Numbers
  | LV    Vname               -- ^ Variables
  | LPlus LExp  LExp          -- ^ Addition
  | LLet  Vname LExp LExp     -- ^ Let binding
  deriving (Show)

-- | `lval l s` takes a let-bound expression and a State and returns the result
--    of evaluating `l` in `s`:

{-@ reflect lval @-}
lval :: LExp -> State -> Int
lval (LN i) _         = i
lval (LV x) s         = get s x
lval (LPlus e1 e2)  s = lval e1 s + lval e2 s
lval (LLet x e1 e2) s = lval e2 (set s x (lval e1 s))

-- | Write a function `inlyne` that converts an `LExp` into a plain `AExp`
--   by "inlining" the let-definitions, i.e. `let x = e1 in e2` should become
--     e2-with-all-occurrences-x-replaced-by-e1

{-@ reflect inlyne @-}
inlyne :: LExp -> AExp
inlyne lexp = replace lexp (init (N 0))


-- NIKI TO FIX
-- The below is required because the sort `GState Int AExp`
-- does not appear in the logic, so apply :: Int -> GState Int AExp
-- was not generated
{-@ reflect help @-}
help :: GState Int AExp
help = init (N 0)

{-@ reflect contains @-}
contains :: (Eq k) => GState k v -> k -> Bool
contains (Bind k v kvs) key
  | key == k   = True
  | otherwise  = contains kvs key
contains _ _  = False

{-@ reflect replace@-}
replace :: LExp -> GState Vname AExp -> AExp
replace (LN i) _ = (N i)
replace (LV x) s = if s `contains` x then get s x else (V x)
replace (LPlus l r) s = Plus (replace l s) (replace r s)
replace (LLet x e1 e2) s = let
  newS = set s x (replace e1 s)
  in
    replace e2 newS

-- Bug also goes away if the below liquid line is commented out.
{-@ lem_inlyne :: l:_ -> s:_ -> { lval l s = aval (inlyne l) s } @-}
lem_inlyne :: LExp -> State -> Proof
lem_inlyne = undefined -- impossible "TODO"

