{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

module MossakaBug where

data Pred
  = Var String
  | Not Pred
  | Or  Pred Pred
  | And Pred Pred

{-@ reflect nnf @-}
nnf :: Pred -> Pred
nnf (Var p) = Var p
nnf (Not (Not p)) = (nnf p)
nnf (And p q) = And (nnf p) (nnf q)
nnf (Or p q) = Or (nnf p) (nnf q)
nnf (Not (And p q)) = Or (nnf $ Not p) (nnf $ Not q)
nnf (Not (Or p q)) = And (nnf $ Not p) (nnf $ Not q)
nnf (Not (Var v)) = Not (Var v)

{-@ lem_nnf :: s:_ -> p:_ -> { pval p s = pval (nnf p) s } @-}
lem_nnf :: BState -> Pred -> ()
lem_nnf s (Var v) = pval (nnf (Var v)) s
    `seq` pval (Var v) s
    `seq` ()
lem_nnf s p = undefined

{-@ reflect pval @-}
pval :: Pred -> BState -> Bool
pval (Var x)     s = get s x
pval (And p1 p2) s = (pval p1 s) && (pval p2 s)
pval (Or  p1 p2) s = (pval p1 s) || (pval p2 s)
pval (Not p)     s = not (pval p s)

{-@ reflect get @-}
get :: BState -> String -> Bool
get s x = True

data BState = BS
