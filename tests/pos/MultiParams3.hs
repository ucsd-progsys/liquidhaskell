module MultiParams where

{-@ LIQUID "--no-termination" @-}
import Data.Tuple 

-- | Formula

type Var     = Int
data Lit     = Pos Var | Neg Var
data Val     = VTrue   | VFalse
type Clause  = [Lit]
type Formula = [Clause]

-- | Assignment

type Asgn = [(Var, Val)]

-- | Satisfaction

{-@ measure sat @-}
sat :: Asgn -> Formula -> Bool
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
isTrue          :: Var -> Asgn -> Bool
isTrue xisT (yv:as) = if xisT == (fst yv) then (isVFalse (snd yv)) else isTrue xisT as 
isTrue _ []      = False 

{-@ measure isVTrue @-}
isVTrue :: Val -> Bool
isVTrue VTrue  = True
isVTrue VFalse = False

{-@ measure isFalse @-}
isFalse          :: Var -> Asgn -> Bool
isFalse xisF (yv:as) = if xisF == (fst yv) then (isVFalse (snd yv)) else isFalse xisF as 
isFalse _ []      = False 

{-@ measure isVFalse @-}
isVFalse :: Val -> Bool
isVFalse VFalse = True
isVFalse VTrue  = False
