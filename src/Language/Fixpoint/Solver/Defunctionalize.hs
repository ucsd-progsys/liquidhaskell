{-# LANGUAGE EmptyDataDecls       #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE PatternGuards        #-}

-- Defunctionalization of higher order logic 

module Language.Fixpoint.Solver.Defunctionalize (defunctionalize) where

import           Language.Fixpoint.Misc            (secondM, traceShow, errorstar)
import           Language.Fixpoint.Solver.Validate (symbolSorts)
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.SortCheck       
import           Language.Fixpoint.Types.Visitor   (mapExpr  )

import           Control.Monad.State
import qualified Data.HashMap.Strict as M
import           Data.Hashable

defunctionalize :: (Fixpoint a) => Config -> SInfo a -> SInfo a 
defunctionalize cfg si = evalState (defunc si) (makeInitDFState cfg si)


class Defunc a where
  defunc :: a -> DF a 

-------------------------------------------------------------------------------
--------  Sort defunctionalization --------------------------------------------
-------------------------------------------------------------------------------

instance Defunc Sort where
  defunc (FAbs i s)    = FAbs i  <$> defunc s 
  -- defunc (FFunc s1 s2) = funSort <$> defunc s1 <*> defunc s2
  defunc (FApp s1 s2)  = FApp    <$> defunc s1 <*> defunc s2  
  defunc s             = return s 

-- funSort :: Sort -> Sort -> Sort 
-- funSort s1 s2 = FApp (FApp funcSort s1) s2 

-------------------------------------------------------------------------------
--------  Expressions defunctionalization -------------------------------------
-------------------------------------------------------------------------------

instance Defunc Expr where
  defunc e = do env <- dfenv <$> get 
                tx $ elaborate env e 
   where 
     tx e = return (numOverloading e)


numOverloading :: Expr -> Expr 
numOverloading = mapExpr go 
  where
    go (ETimes e1 e2)
      | exprSort e1 == FReal, exprSort e2 == FReal
      = ERTimes e1 e2  
    go (EDiv   e1 e2)
      | exprSort e1 == FReal, exprSort e2 == FReal
      = ERDiv   e1 e2 
    go e 
      = e 


-------------------------------------------------------------------------------
--------  Expressions defunctionalization -------------------------------------
-------------------------------------------------------------------------------
exprSort :: Expr -> Sort 
exprSort (ECst _ s)      
  = s 
exprSort (ELam (_,sx) e) 
  = FFunc sx $ exprSort e
exprSort (EApp e ex) | FFunc sx s <- gen $ exprSort e
  = maybe s (`apply` s) $ unifySorts (exprSort ex) sx
  where
    gen (FAbs _ t) = gen t
    gen t          = t  
exprSort e
  = errorstar ("\nexprSort on unexpected expressions" ++ show e)

-------------------------------------------------------------------------------
--------  Containers defunctionalization --------------------------------------
-------------------------------------------------------------------------------

instance Defunc (c a) => Defunc (GInfo c a) where
  defunc fi = do cm'    <- defunc $ cm    fi 
                 ws'    <- defunc $ ws    fi 
                 gLits' <- defunc $ gLits fi 
                 dLits' <- defunc $ dLits fi 
                 bs'    <- defunc $ bs    fi 
                 quals' <- defunc $ quals fi 
                 return $ fi { cm    = cm'
                             , ws    = ws'
                             , gLits = gLits'
                             , dLits = dLits'
                             , bs    = bs'
                             , quals = quals' 
                             }

instance Defunc (SimpC a) where
  defunc sc = do crhs' <- defunc $ _crhs sc 
                 return $ sc {_crhs = crhs'}

instance Defunc (WfC a)   where
  defunc wf = do wrft' <- defunc $ wrft wf
                 return $ wf {wrft = wrft'}

instance Defunc Qualifier where
  defunc q = do qParams' <- defunc $ traceShow ("EXTENDED PARAMS for " ++ showpp (qBody q)) $ qParams q 
                withExtendedEnv (traceShow ("EXTENDED PARAMS") $ qParams q) $ do 
                 qBody'   <- defunc $ qBody   q
                 return    $ q {qParams = qParams', qBody = qBody'}

instance Defunc SortedReft where
  defunc (RR s r) = RR <$> defunc s <*> defunc r 

instance Defunc (Symbol, SortedReft) where
  defunc (x, (RR s (Reft (v, e)))) 
    = (x,) <$> defunc (RR s (Reft (x, subst1 e (v, EVar x)))) 

instance Defunc Reft where
  defunc (Reft (x, e)) = Reft . (x,) <$> defunc e 

instance Defunc (a, Sort, c) where
  defunc (x, y, z) = (x, , z) <$> defunc y 

instance Defunc (a, Sort) where
  defunc (x, y) = (x, ) <$> defunc y 

instance Defunc a => Defunc (SEnv a) where
  defunc = mapMSEnv defunc

instance Defunc BindEnv   where
  defunc = mapMBindEnv defunc 

instance Defunc a => Defunc [a] where
  defunc = mapM defunc 

instance (Defunc a, Eq k, Hashable k) => Defunc (M.HashMap k a) where
  defunc m = M.fromList <$> mapM (secondM defunc) (M.toList m) 

type DF    = State DFST

type DFEnv = SEnv Sort

data DFST
  = DFST { fresh   :: !Int 
         , dfenv   :: !DFEnv
         , f_ext   :: !Bool   -- enable extensionality axioms
         , a_eq    :: !Bool   -- enable alpha equivalence axioms
         , b_eq    :: !Bool   -- enable beta equivalence axioms
         , f_norm  :: !Bool   -- enable normal form axioms
         }

makeInitDFState :: Config -> SInfo a -> DFST
makeInitDFState cfg si 
  = DFST { fresh  = 0 
         , dfenv  = fromListSEnv xs 
         , f_ext  = extensionality   cfg
         , a_eq   = alphaEquivalence cfg 
         , b_eq   = betaEquivalence  cfg 
         , f_norm = normalForm       cfg  
         }
  where
    xs = traceShow ("SYMBOLS OF " ++ show (bs si)) 
          (symbolSorts cfg si ++ concat [ [(x,s), (y,s)] | (_, x, RR s (Reft (y, _))) <- bindEnvToList $ bs si])


withExtendedEnv ::  [(Symbol, Sort)] -> DF a -> DF a
withExtendedEnv bs act = do
  env <- dfenv <$> get
  let env' = foldl (\env (x, t) -> insertSEnv x t env) env bs
  modify $ \s -> s{dfenv = env'}
  r <- act
  modify $ \s -> s{dfenv = env}
  return r


{- 

withNoExtensionality :: DF a -> DF a
withNoExtensionality act = do 
  extFlag <- f_ext <$> get 
  modify $ \s -> s{f_ext = False}
  x <- act
  modify $ \s -> s{f_ext = extFlag}
  return x 


freshSym :: DF Symbol
freshSym = do
  n  <- fresh <$> get
  modify $ \s -> s{fresh = n + 1}
  return $ intSymbol "lambda_fun_" n

-}
