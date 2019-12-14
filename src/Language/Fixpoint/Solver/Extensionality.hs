{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternGuards        #-}

module Language.Fixpoint.Solver.Extensionality (expand) where

import           Control.Monad.State
import qualified Data.HashMap.Strict       as M

import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor (mapMExpr)

expand :: SymEnv -> SInfo a -> SInfo a
expand senv si = evalState (expend si) $ initST senv 


class Expend a where
  expend :: a -> Ex a


instance Expend (SInfo a) where
  expend si = do 
    setBEnv (bs si)
    cm'      <- expend (cm si) 
    bs'      <- exbenv <$> get  
    return $ si{ cm = cm' , bs = bs' }

instance (Expend a) => Expend (M.HashMap SubcId a) where 
  expend h = M.fromList <$> mapM expend (M.toList h) 

instance (Expend a, Expend b) => Expend (a,b) where 
  expend (a,b) = (,) <$> expend a <*> expend b 

instance Expend SubcId where
  expend i = return i 

instance Expend (SimpC a) where
  expend c = do 
    setExBinds 
    rhs <- expend (_crhs c)
    is <- exbinds <$> get 
    return $ c{_crhs = rhs, _cenv = fromListIBindEnv is `unionIBindEnv` _cenv c}


instance Expend Expr where 
  expend = mapMExpr go 
    where  
      go (PAtom b e1 e2)
       | (b == Eq || b == Ne)
       , Just s <- bkFFunc (exprSort "extensionality" e1)
       = do let ss   = init $ snd s
            xs      <- mapM freshArg ss 
            env     <- exenv <$> get 
            let e1'  = eApps (unElab e1) (EVar <$> xs) 
            let e2'  = eApps (unElab e2) (EVar <$> xs) 
            let elab = elaborate (dummyLoc "extensionality") env
            return   $ PAtom b (elab e1') (elab e2')
      go e = return e 

      
type Ex    = State ExSt
data ExSt = ExSt { unique :: Int, exenv :: SymEnv, exbenv :: BindEnv, exbinds :: [BindId] }

initST :: SymEnv -> ExSt
initST env = ExSt 0 env mempty mempty 


setBEnv :: BindEnv -> Ex () 
setBEnv benv = modify (\st -> st{exbenv = benv})

setExBinds :: Ex ()
setExBinds = modify (\st -> st{exbinds = []})

freshArg :: Sort -> Ex Symbol
freshArg s = do 
  st   <- get 
  let x = symbol ("ext$" ++ show (unique st))
  let (id, benv') = insertBindEnv x (trueSortedReft s) (exbenv st)
  modify (\st -> st{exenv = insertSymEnv x s (exenv st), exbenv = benv', exbinds = id:exbinds st })
  return x 
