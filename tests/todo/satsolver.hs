module SatSolver where

-- | Formula

type Var     = Int
data Lit     = Pos Var | Neg Var
type Clause  = [Lit]
type Formula = [Clause]

-- | Assignment

type Asgn = [(Var, Bool)]


-- | Top-level "solver"

{-@ solve :: f:_ -> Maybe {a:Asgn | sat a f} @-}
solve   :: Formula -> Maybe Asgn
solve f = find (\a -> sat a f) (asgns f) 

find :: (a -> Bool) -> [a] -> Maybe a
find f [] = False
find f (x:xs) | f x       = Just x 
              | otherwise = Nothing 
-- | Generate all assignments

asgns :: Formula -> [Asgn] -- generates all possible T/F vectors
asgns = undefined 
 

-- | Satisfaction

{-@ measure sat @-}
sat :: Formula ->  [Asgn] -> Bool
sat a []         = True
sat a (c:cs)     = satCls a c && sat a cs

{-@ measure satCls @-}
satCls :: Asgn -> Clause -> Bool
satCls a []      = False
satCls a (l:ls)  = satLit a l || satCls a ls

{-@ measure satLit @-}
satLit :: Asgn -> Lit -> Bool
satLit a (Pos x) = isTrue x a 
satLit a (Neg x) = isFalse x a

{-@ measure isTrue @-}
isTrue           :: Var -> Asgn -> Bool
isTrue x ((y, v):as)  = if x == y then v else isTrue x as 
isTrue _ []           = False 

{-@ measure isFalse @-}
isFalse          :: Var -> Asgn -> Bool
isFalse x ((y, v):as) = if x == y then not v else isFalse x as 
isFalse _ []          = False 

