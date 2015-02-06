module SatSolver where

{-@ LIQUID "--no-termination" @-}

-- | Formula

type Var     = Int
data Lit     = Pos Var | Neg Var
type Clause  = [Lit]
type Formula = [Clause]

-- | Assignment

type Asgn = [(Var, Bool)]

-- | Top-level "solver"

{-@ solve :: f:_ -> Maybe {a:Asgn | Prop (sat a f)} @-}
solve   :: Formula -> Maybe Asgn
solve f = go (asgns f)
  where
  	go []     = Nothing
  	go (x:xs) | sat x f = Just x
  	          | otherwise = go xs 

-- | Generate all assignments

asgns :: Formula -> [Asgn] -- generates all possible T/F vectors
asgns = undefined
 

-- | Satisfaction

{-@ measure sat :: Asgn -> Formula -> Bool @-}
sat :: Asgn -> Formula -> Bool
{-@ sat :: a:Asgn -> f:Formula -> {v:Bool | Prop (sat a f)} @-}
sat a []         = True
sat a (c:cs)     = satCls a c && sat a cs

{- measure satCls @-}
satCls :: Asgn -> Clause -> Bool
satCls a []      = False
satCls a (l:ls)  = satLit a l || satCls a ls

{- measure satLit @-}
satLit :: Asgn -> Lit -> Bool
satLit a (Pos x) = isTrue x a 
satLit a (Neg x) = isFalse x a

{- measure isTrue @-}
isTrue           :: Var -> Asgn -> Bool
isTrue x ((y, v):as)  = if x == y then v else isTrue x as 
isTrue _ []           = False 

{- measure isFalse @-}
isFalse          :: Var -> Asgn -> Bool
isFalse x ((y, v):as) = if x == y then not v else isFalse x as 
isFalse _ []          = False




