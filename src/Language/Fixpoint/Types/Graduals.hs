{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TupleSections              #-}

-- | This module contains the top-level SOLUTION data types,
--   including various indices used for solving.

module Language.Fixpoint.Types.Graduals (
  uniquify, 

  makeSolutions, 

  GSol,

  Gradual (..)
  ) where 

import Language.Fixpoint.Types.Refinements
import Language.Fixpoint.Types.Constraints
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Types.PrettyPrint
import Language.Fixpoint.Types.Environments
import Language.Fixpoint.Types.Substitutions
import Language.Fixpoint.Types.Visitor
import Language.Fixpoint.Types.Sorts
import Language.Fixpoint.Types.Names        (gradIntSymbol, tidySymbol)
import Language.Fixpoint.Misc               (allCombinations)

import Control.DeepSeq

import qualified Data.HashMap.Strict       as M
import qualified Data.List                 as L

import Control.Monad.State.Lazy 
import Data.Maybe (fromMaybe)
import qualified Language.Fixpoint.SortCheck       as So
import Language.Fixpoint.Solver.Sanitize (symbolEnv)


data GSol = GSol (SEnv Sort) (M.HashMap KVar Expr)

instance Show GSol where
  show (GSol _ m) = "GSOL = \n" ++ unlines ((\(k,e) -> showpp k ++ " |-> " ++ showpp (tx e)) <$> M.toList m)
    where
      tx e = subst (mkSubst $ [(x, EVar $ tidySymbol x) | x <- syms e]) e


makeSolutions :: (NFData a, Fixpoint a) 
              => Config -> SInfo a 
              -> [(KVar, ((b, Expr), [[Expr]]))]
              -> [GSol]
makeSolutions cfg fi kes 
  = map (GSol env . M.fromList) (allCombinations (go  <$> kes))
  where
    go (k, ((_,e), es)) = [(k, pAnd (e:e')) | e' <- es]
    env = symbolEnv cfg fi 


-------------------------------------------------------------------------------
-- |  Make each gradual appearence unique -------------------------------------
-------------------------------------------------------------------------------
uniquify :: (NFData a, Fixpoint a) => SInfo a -> (SInfo a)

uniquify fi = fi{cm = cm', ws = ws', bs = bs'}
  where 
  (cm', km, bs') = uniquifyCS (bs fi) (cm fi)
  ws'            = expandWF km (ws fi)       

uniquifyCS :: (NFData a, Fixpoint a) 
           => BindEnv
           -> M.HashMap SubcId (SimpC a) 
           -> (M.HashMap SubcId (SimpC a), M.HashMap KVar [KVar], BindEnv)
uniquifyCS bs cs 
  = (x, kmap st, benv st) 
  where
    (x, st) = runState (uniq cs) (initUniqueST bs)

class Unique a where 
   uniq :: a -> UniqueM a 

instance Unique a => Unique (M.HashMap SubcId a) where
  uniq m = M.fromList <$> mapM (\(i,x) -> (i,) <$> uniq x) (M.toList m)

instance Unique (SimpC a) where
  uniq cs = do 
    rhs <- uniq (_crhs cs)
    env <- uniq (_cenv cs)
    return cs{_crhs = rhs, _cenv = env}

instance Unique IBindEnv where
  uniq env = emptyCache >> (fromListIBindEnv <$> mapM uniq (elemsIBindEnv env))

instance Unique BindId where
  uniq i = do 
    bs <- benv <$> get 
    let (x, t) = lookupBindEnv i bs 
    resetChange
    t' <- uniq t 
    hasChanged <- change <$> get 
    if hasChanged
      then do let (i', bs') = insertBindEnv x t' bs  
              updateBEnv bs'
              return i'
      else return i

instance Unique SortedReft where
  uniq (RR s r) = RR s <$> uniq r  

instance Unique Reft where
  uniq (Reft (x,e)) = (Reft . (x,)) <$> uniq e 

instance Unique Expr where
  uniq = mapMExpr go 
   where 
    go (PGrad k su e) = do 
      k' <- freshK k 
      return $ PGrad k' su e  
    go e              = return e 

-------------------------------------------------------------------------------
-- | The Unique Monad ---------------------------------------------------------
-------------------------------------------------------------------------------

type UniqueM = State UniqueST 
data UniqueST 
  = UniqueST { freshId :: Integer
             , kmap    :: M.HashMap KVar [KVar]
             , change  :: Bool 
             , cache   :: M.HashMap KVar KVar 
             , benv    :: BindEnv 
             }

emptyCache :: UniqueM ()
emptyCache = modify $ \s -> s{cache = mempty}

addCache :: KVar -> KVar -> UniqueM ()
addCache k k' = modify $ \s -> s{cache = M.insert k k' (cache s)}

updateBEnv :: BindEnv -> UniqueM ()
updateBEnv bs = modify $ \s -> s{benv = bs}

setChange :: UniqueM ()
setChange = modify $ \s -> s{change = True}

resetChange :: UniqueM ()
resetChange = modify $ \s -> s{change = False}

initUniqueST :: BindEnv ->  UniqueST
initUniqueST = UniqueST 0 mempty False mempty

freshK, freshK' :: KVar -> UniqueM KVar
freshK k  = do
  cached <- cache <$> get 
  case M.lookup k cached of 
    {- OPTIMIZATION: Only create one fresh occurence of ? per constraint environment. -}
    Just k' -> return  k' 
    Nothing -> freshK' k 

freshK' k = do 
  i <- freshId <$> get 
  modify $ (\s -> s{freshId = i + 1})
  let k' = KV $ gradIntSymbol i 
  addK k k' 
  setChange 
  addCache k k'
  return k'

addK :: KVar -> KVar -> UniqueM ()
addK key val = 
  modify $ (\s -> s{kmap = M.insertWith (++) key [val] (kmap s)})

-------------------------------------------------------------------------------
-- | expandWF -----------------------------------------------------------------
-------------------------------------------------------------------------------

expandWF :: (NFData a, Fixpoint a)
         => M.HashMap KVar [KVar]
         -> M.HashMap KVar (WfC a)
         -> M.HashMap KVar (WfC a)
expandWF km ws 
  = M.fromList $ 
       ([(k, updateKVar k w) | (i, w) <- gws, (kw, ks) <- km', kw == i, k <- ks]
        ++ kws)
  where
    (gws, kws)       = L.partition (isGWfc . snd) $ M.toList ws
    km'              = M.toList km 
    updateKVar k wfc = wfc {wrft = (\(v,s,_) -> (v,s,k)) $ wrft wfc}

-------------------------------------------------------------------------------
-- |  Substitute Gradual Solution ---------------------------------------------
-------------------------------------------------------------------------------

class Gradual a where
  gsubst :: GSol -> a -> a 

instance Gradual Expr where
  gsubst (GSol env m) = mapKVars' (\(k, _) -> Just (fromMaybe mempty $ So.elaborate "initBGind.mkPred" env $ M.lookup k m))

instance Gradual Reft where
  gsubst su (Reft (x, e)) = Reft (x, gsubst su e)

instance Gradual SortedReft where
  gsubst su r = r {sr_reft = gsubst su (sr_reft r)}

instance Gradual (SimpC a) where
  gsubst su c = c {_crhs = gsubst su (_crhs c)}

instance Gradual BindEnv where
  gsubst su = mapBindEnv (\_ (x, r) -> (x, gsubst su r))

instance Gradual v => Gradual (M.HashMap k v) where
  gsubst su = M.map (gsubst su)

instance Gradual (SInfo a) where
  gsubst su fi = fi { bs = gsubst su (bs fi)
                    , cm = gsubst su (cm fi)
                    }



