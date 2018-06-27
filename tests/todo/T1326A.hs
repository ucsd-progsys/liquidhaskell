{-@ LIQUID "--reflection"  @-}

module T1326A where


data Term l 
  = TTrue 
  | TFalse
  | TLabel l
  | TLOp LabelOp (Term l) (Term l) 
  | TLabeled l (Term l)
  | THole 

{-@ data Term [tsize] @-}

{-@ invariant {v:Term l | isTLabel v <=> is$T1326A.TLabel v} @-}
{-@ measure isTLabel @-}
isTLabel :: Term l -> Bool 
isTLabel (TLabel _) = True 
isTLabel _          = False 

{-@ reflect boolTerm @-}
boolTerm :: Bool -> Term l
boolTerm True = TTrue
boolTerm False = TFalse 


data LabelOp = LMeet | LJoin | LCanFlowTo

{-@ measure tsize @-}
tsize :: Term l -> Int
{-@ tsize :: Term l -> Nat @-}
tsize TTrue          = 0
tsize TFalse         = 0
tsize (TLabel _)     = 0
tsize (TLOp _ t1 t2) = 1 + tsize t1 + tsize t2
tsize (TLabeled _ t) = 1 + tsize t 
tsize THole          = 0


