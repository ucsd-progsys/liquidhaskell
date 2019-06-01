module Language.Haskell.Liquid.Synthesize (
    synthesize
  ) where

import           Language.Haskell.Liquid.Types hiding (SVar)
import           Language.Haskell.Liquid.Constraint.Types
import qualified Language.Haskell.Liquid.Types.RefType as R
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Types hiding (SEnv, SVar)
import qualified Language.Fixpoint.Types.Config as F

import           Text.PrettyPrint.HughesPJ ((<+>), text, char)

import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Data.Default 
import qualified Data.Text as T
import           Data.Maybe
import           Debug.Trace 

type SSEnv = M.HashMap Symbol SpecType

synthesize :: FilePath -> F.Config -> CGInfo -> SSEnv -> SpecType -> IO [SExpr]
synthesize tgt fcfg cgi ctx t = (:[]) <$> evalSM (go t) tgt fcfg cgi ctx
  where 

    -- Is it good to push and pop here or in (1)??
    pushContext :: SpecType -> StateT SState IO SExpr
    pushContext t = do
      ctx <- sContext <$> get
      liftIO $ SMT.smtPush ctx
      sexpr <- go t
      liftIO $ SMT.smtPop ctx
      return sexpr


    go :: SpecType -> StateT SState IO SExpr
    -- Type Variable
    go (RVar α _)        = (`synthesizeRVar` α) <$> getSEnv
    -- Function 
    go (RFun x tx t _)   = 
        do  let RR s (Reft (pn, in_rr)) = rTypeSortedReft (tyConEmbed cgi) tx  
            y <- freshVar 
            addEnv y tx 

            ctx <- sContext <$> get
            -- (1)
            liftIO $ SMT.smtPush ctx
            liftIO $ SMT.smtDecl ctx y s
            liftIO $ SMT.smtAssert ctx (substInFExpr pn y in_rr)
            -- liftIO $ SMT.smtCheckSat ctx in_rr
            sexpr <- go (t `subst1` (x, EVar y))
            liftIO $ SMT.smtPop ctx
            return $ SFun y sexpr 

    -- Type Abstraction 
    go (RAllT _ t)       = go t
    -- Data Type, e.g., c = Int and ts = [] or c = List and ts = [a] 
    go t@(RApp c _ts _ r)  
      | R.isNumeric (tyConEmbed cgi) c = 
          do  let RR s (Reft(x,rr)) = rTypeSortedReft (tyConEmbed cgi) t 
              ctx <- sContext <$> get 
              liftIO $ SMT.smtPush ctx
              liftIO $ SMT.smtDecl ctx x s
              liftIO $ SMT.smtCheckSat ctx rr 
              -- Get model and parse the value of x
              SMT.Model modelBinds <- liftIO $ SMT.smtGetModel ctx
              
              let xNotFound = error $ "Symbol " ++ show x ++ "not found."
                  smtVal = T.unpack (fromMaybe xNotFound $ lookup x modelBinds)

              liftIO (SMT.smtPop ctx)
              return $ tracepp ("numeric with " ++ show r) (SVar $ symbol smtVal)
              -- return def
    go (RApp _c _ts _ _) 
      = return def 
    -- Type Application, e.g, m a 
    go RAppTy{} = return def 


    -- Fancy Liquid Types to be ignored for now since they do not map to haskell types
    go (RImpF _ _ t _) = go t 
    go (RAllP _ t)     = go t 
    go (RAllS _ t)     = go t 
    go (RAllE _ _ t)   = go t 
    go (REx _ _ t)     = go t 
    go (RRTy _ _ _ t)  = go t 
    go (RExprArg _)    = return def 
    go (RHole _)       = return def 

------------------------------------------------------------------------------
-- Handle dependent arguments
------------------------------------------------------------------------------
-- * Arithmetic refinement expressions: 
--    > All constants right, all variables left
------------------------------------------------------------------------------
-- depsSort :: Expr -> Expr 
-- depsSort e = 
--   case e of 
--     PAnd exprs -> PAnd (map depsSort exprs)
--       -- error "PAnd not implemented yet"
--     PAtom brel e1 e2 -> PAtom brel (depsSort e1)
--       -- error ("e1 = " ++ show e1)
--       -- error "PAtom not implemented yet"
--     ESym _symConst -> error "ESym not implemented yet" 
--     constant@(ECon _c) -> constant 
--     EVar _symbol -> error "EVar not implemented yet"
--     EApp _expr1 _expr2 -> error "EVar not implemented yet"
--     ENeg _expr -> error "ENeg not implemented yet"
--     EBin _bop _expr1 _expr2 -> error "EBin not implemented yet"
--     EIte _expr1 _expr2 _expr3 -> error "EIte not implemented yet"
--     ECst _expr _sort -> error "ECst not implemented yet"
--     ELam _targ _expr -> error "ELam not implemented yet"
--     ETApp _expr _sort -> error "ETApp not implemented yet"
--     ETAbs _expr _symbol -> error "ETAbs not implemented yet"
--     POr _exprLst -> error "POr not implemented yet" 
--     PNot _expr -> error "PNot not implemented yet"
--     PImp _expr1 _expr2 -> error "PImp not implemented yet"
--     PIff _expr1 _expr2 -> error "PIff not implemented yet"
--     PKVar _kvar _subst -> error "PKVar not implemented yet"
--     PAll _ _expr -> error "PAll not implemented yet"
--     PExist _ _expr -> error "PExist not implemented yet" 
--     PGrad _kvar _subst _gradInfo _expr -> error "PGrad not implemented yet"
--     ECoerc _sort1 _sort2 _expr -> error "ECoerc not implemented yet"

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

data SState = SState {ssEnv :: SSEnv, ssIdx :: Int, sContext :: SMT.Context}
type SM = StateT SState IO

evalSM :: SM a -> FilePath -> F.Config -> CGInfo -> SSEnv -> IO a 
evalSM act tgt fcfg cgi env = do 
  ctx <- SMT.makeContext fcfg tgt  
  r <- evalStateT act (SState env 0 ctx)
  SMT.cleanupContext ctx 
  return r 

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

-- The rest will be added when needed.
-- Replaces    | old w   | new  | symbol name in expr.
substInFExpr :: Symbol -> Symbol -> Expr -> Expr
substInFExpr pn nn e = 
  case e of 
    PAnd exprs -> PAnd (map (substInFExpr pn nn) exprs)
    PAtom brel e1 e2 -> 
      PAtom brel (substInFExpr pn nn e1) (substInFExpr pn nn e2) 
    ESym _symConst -> error "ESym not implemented yet"
    constant@ECon{} -> constant
    var@(EVar symb) ->
      if symb == pn 
        then EVar nn
        else var
    EApp e1 e2 -> EApp (substInFExpr pn nn e1) (substInFExpr pn nn e2)
    ENeg e -> ENeg (substInFExpr pn nn e) 
    EBin bop e1 e2 -> EBin bop (substInFExpr pn nn e1) (substInFExpr pn nn e2) 
    EIte e1 e2 e3 -> 
      EIte (substInFExpr pn nn e1) (substInFExpr pn nn e2) (substInFExpr pn nn e3)
    ECst e s -> ECst (substInFExpr pn nn e) s
    ELam targ e -> ELam targ (substInFExpr pn nn e)
    ETApp e s -> ETApp (substInFExpr pn nn e) s 
    ETAbs e sym -> ETAbs (substInFExpr pn nn e) sym
    POr _exprLst -> error "POr not implemented yet" 
    PNot _expr -> error "PNot not implemented yet"
    PImp _expr1 _expr2 -> error "PImp not implemented yet"
    PIff _expr1 _expr2 -> error "PIff not implemented yet"
    PKVar _kvar _subst -> error "PKVar not implemented yet"
    PAll _ _expr -> error "PAll not implemented yet"
    PExist _ _expr -> error "PExist not implemented yet" 
    PGrad _kvar _subst _gradInfo _expr -> error "PGrad not implemented yet"
    ECoerc _sort1 _sort2 _expr -> error "ECoerc not implemented yet"  