module Language.Haskell.Liquid.Termination.Structural (

  terminationCheck

  ) where 

import Language.Haskell.Liquid.Types hiding (terminationCheck)
import Language.Fixpoint.Types.Errors
import Language.Haskell.Liquid.GHC.Misc (showPpr)
import Language.Haskell.Liquid.Types.Visitors 

import CoreSyn
import Var
import Name (getSrcSpan)

import Text.PrettyPrint.HughesPJ
import qualified Data.HashSet                           as S
import qualified Data.List                              as L


terminationCheck :: GhcInfo -> Output Doc 
terminationCheck info = mconcat $ map (resultToDoc . checkBind (cbs info)) (S.toList $ gsStTerm $ spec info)


data Result = OK | Error [UserError] 

instance Monoid Result where
  mempty = OK 
  mappend OK e = e 
  mappend e OK = e 
  mappend (Error e1) (Error e2) = Error (e1 ++ e2)

resultToDoc :: Result -> Output Doc 
resultToDoc OK        = mempty
resultToDoc (Error x) = mempty {o_result = Unsafe x }

checkBind :: [CoreBind] -> Var -> Result  
checkBind cbs x = maybe OK isInductive (findRecBind cbs x)


findRecBind :: [CoreBind] -> Var -> Maybe [(Var,CoreExpr)]
findRecBind [] _ = Nothing 
findRecBind (NonRec x _:_) y | x == y 
  = Nothing 
findRecBind (Rec xes:_)    y | y `elem` (fst <$> xes) 
  = Just xes 
findRecBind (_:xes) y
  = findRecBind xes y

isInductive :: [(Var,CoreExpr)] -> Result
isInductive xes = mconcat (checkInductive <$> xes)

checkInductive :: (Var, CoreExpr) -> Result
checkInductive (x, e) 
  | length xs /= 1
  = err (text  "check inductive on function with many arguments!")
  | Case _ _ _ alts <- e'
  , (bs, is)        <- L.partition (isBaseCase x) alts 
  , is'             <- filter (not . null) (map (nonInductiveCalls x (length ts)) is)
  = if null bs then err (text "The definition has no base case.")
    else if not (null is') then err (text "The definition contains non inductive calls: " <+> (text $ showPpr is'))
    else OK
  | otherwise 
  = err (text "The definition should be a function followed by case analysis.")
  where
    (ts, xs, e') = collectTyAndValBinders e
    err expl = Error [ErrStTerm (getSrcSpan x) (text $ showPpr x) expl]


nonInductiveCalls :: Var -> Int -> (AltCon, [Var], CoreExpr) -> [CoreExpr] 
nonInductiveCalls f i (_, xs, e) = go e 
  where
    go (App g e) | isRecCall i g , not (isSmallerArg e) = [App g e]
    go (Let (NonRec _ ex) e) = go ex ++ go e
    go (Let (Rec xes) e)     = concatMap go (e:(snd <$> xes)) ++ go e
    go (Tick _ e)            = go e 
    go (App e1 e2)           = go e1 ++ go e2 
    go (Lam _ e)             = go e 
    go (Cast e _)            = go e 
    go (Case e _ _ alt)      = go e ++ concat [go e' | (_, _, e') <- alt]
    go _ = []    

    isRecCall 0 (Var g)    = f == g
    isRecCall i (Tick _ e) = isRecCall i e 
    isRecCall i (App f _)  = isRecCall (i-1) f
    isRecCall _ _          = False 

    isSmallerArg (Var x)    = x `elem` xs 
    isSmallerArg (Tick _ e) = isSmallerArg e 
    isSmallerArg _          = False 


isBaseCase :: Var -> (a, b, CoreExpr) -> Bool 
isBaseCase x (_, _, e) = (not (x `elem` freeVars mempty e))

