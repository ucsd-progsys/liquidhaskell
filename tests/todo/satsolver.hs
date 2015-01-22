module SatSolver where

-- | Formula

type Var     = Int
data Lit     = Pos Var | Neg Var
data Clause  = [Lit]
data Formula = [Clause]

-- | Assignment

type Asgn = [(Var, Bool)]


-- | Top-level "solver"

{-@ solve :: f:_ -> Maybe {a:Asgn | sat a f} @-}
solve   :: Formula -> Maybe Asgn
solve f = find (\a -> sat a f) (asgns f) 

-- | Generate all assignments

asgns :: Formula -> [Asgn] -- generates all possible T/F vectors
asgns = undefined 
 

-- | Satisfaction

{-@ measure sat @-}
sat a []         = True
sat a (c:cs)     = satCls a && sat a cs

{-@ measure satCls @-}
satCls a []      = False
satCls a (l:ls)  = satLit a l || satCls a ls

{-@ measure satLit @-}
satLit a (Pos x) = isTrue x a 
satLit a (Neg x) = isFalse x a

{-@ measure isTrue @-}
isTrue           :: Var -> Asgn -> Bool
isTrue x (a:as)  = if x == y then v else isTrue x as 
  where
    y            = fst a
    v            = snd a
isTrue _ []      = False 

{-@ measure isFalse @-}
isFalse x (a:as) = if x == y then not v else isFalse x as 
  where
    y            = fst a
    v            = snd a
isFalse _ []     = False 

