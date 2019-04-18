module Language.Haskell.Liquid.Synthesize (
    synthesize
  ) where

import           Language.Haskell.Liquid.Types hiding (SVar)
import           Language.Fixpoint.Types hiding (SEnv, SVar)

import           Text.PrettyPrint.HughesPJ ((<+>), text, char)

import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Data.Default 

type SSEnv = M.HashMap Symbol SpecType

synthesize :: SSEnv -> SpecType -> [SExpr]
synthesize ctx t = [evalState (go t) (initState ctx)]
  where 
    -- Type Variable
    go (RVar α _)        = (`synthesizeRVar` α) <$> getSEnv
    -- Function 
    go (RFun x tx t _)   = do y <- freshVar 
                              addEnv y tx 
                              SFun y <$> go (t `subst1` (x, EVar y))
    -- Type Abstraction 
    go (RAllT _ t)       = go t
    -- Data Type, e.g., c = Int and ts = [] or c = List and ts = [a] 
    go (RApp _c _ts _ _) = return def 
    -- Type Application, e.g, m a 
    go (RAppTy _ _ _)  = return def 


    -- Fancy Liquid Types to be ignored for now since they do not map to haskell types
    go (RImpF _ _ t _) = go t 
    go (RAllP _ t)     = go t 
    go (RAllS _ t)     = go t 
    go (RAllE _ _ t)   = go t 
    go (REx _ _ t)     = go t 
    go (RRTy _ _ _ t)  = go t 
    go (RExprArg _)    = return def 
    go (RHole _)       = return def 


synthesizeRVar :: SSEnv -> RTyVar -> SExpr
synthesizeRVar ctx α = case M.keys $ M.filter isMyVar ctx of
                        []    -> def 
                        (x:_) -> SVar x 
  where 
    isMyVar (RVar β _) = β == α 
    isMyVar _          = False 

-------------------------------------------------------------------------------
-- | Expressions to be Synthesized --------------------------------------------
-------------------------------------------------------------------------------

-- The synthesized expressions currently are only variables and lambdas
-- application, type abstraction and applications might be needed 

data SExpr 
  = SVar Symbol
  | SFun Symbol SExpr 

splitSFun :: SExpr -> ([Symbol], SExpr)
splitSFun = go [] 
  where go ac (SFun x e) = go (x:ac) e 
        go ac e          = (reverse ac, e)

instance PPrint SExpr where 
    pprintTidy k (SVar s)   = pprintTidy k s 
    pprintTidy k (SFun x e) = char '\\' <> (printArgs (x:xs) <+> text "->" <+> pprintTidy k bd) 
      where (xs,bd) = splitSFun e 
            printArgs [] = mempty
            printArgs (x:xs) = pprintTidy k x <+> printArgs xs


instance Default SExpr where 
    def = SVar $ symbol "_todo"

-------------------------------------------------------------------------------
-- | Synthesis Monad ----------------------------------------------------------
-------------------------------------------------------------------------------

-- The state keeps a unique index for generation of fresh variables 
-- and the environment of variables to types that is expanded on lambda terms

data SState = SState {ssEnv :: SSEnv, ssIdx :: Int}
type SM = State SState 

initState :: SSEnv -> SState
initState ctx = SState ctx 0 

getSEnv :: SM SSEnv
getSEnv = ssEnv <$> get 

addEnv :: Symbol -> SpecType -> SM ()
addEnv x t = modify (\s -> s {ssEnv = M.insert x t (ssEnv s)})

freshVar :: SM Symbol
freshVar = (\i -> symbol ("x" ++ show i)) <$> incrSM
              
incrSM :: SM Int 
incrSM = do s <- get 
            put s{ssIdx = ssIdx s + 1}
            return (ssIdx s)
