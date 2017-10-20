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

module Gradual.Uniquify (uniquify) where

import Language.Fixpoint.Types.Refinements
import Language.Fixpoint.Types.Constraints
import Language.Fixpoint.Types.PrettyPrint
import Language.Fixpoint.Types.Environments
import Language.Fixpoint.Types.Visitor
import Language.Fixpoint.Types.Spans
import Language.Fixpoint.Types.Names        (gradIntSymbol)

import Control.DeepSeq

import qualified Data.HashMap.Strict       as M
import qualified Data.List                 as L

import Control.Monad.State.Lazy

import Gradual.Types (GSpan)

-------------------------------------------------------------------------------
-- |  Make each gradual appearence unique -------------------------------------
-------------------------------------------------------------------------------

uniquify :: (NFData a, Fixpoint a, Loc a) => SInfo a -> (GSpan, SInfo a)

uniquify fi = (km', fi{cm = cm', ws = ws', bs = bs'})
  where
  (cm', km, bs') = uniquifyCS (bs fi) (cm fi)
  ws'            = expandWF km (ws fi)
  km'            = M.union km $ M.map (const []) $ M.filter isGradual (ws fi)

uniquifyCS :: (NFData a, Fixpoint a, Loc a)
           => BindEnv
           -> M.HashMap SubcId (SimpC a)
           -> (M.HashMap SubcId (SimpC a), GSpan, BindEnv)
uniquifyCS bs cs = (x, km, benv st)
  where
    (x, st) = runState (uniq cs) (initUniqueST bs)
    km      = kmap st

class Unique a where
   uniq :: a -> UniqueM a

instance Unique a => Unique (M.HashMap SubcId a) where
  uniq m = M.fromList <$> mapM (\(i,x) -> (i,) <$> uniq x) (M.toList m)

instance Loc a => Unique (SimpC a) where
  uniq cs = do
    updateLoc $ srcSpan $ _cinfo cs
    rhs <- uniq (_crhs cs)
    env <- uniq (_cenv cs)
    return cs{_crhs = rhs, _cenv = env}

instance Unique IBindEnv where
  uniq env = withCache (fromListIBindEnv <$> mapM uniq (elemsIBindEnv env))

instance Unique BindId where
  uniq i = do
    bs <- benv <$> get
    let (x, t) = lookupBindEnv i bs
    resetChange
    t' <- uniq t
    hasChanged <- change <$> get
    if hasChanged
      then do let (i', bs') = insertBindEnv x t' bs
              updateBEnv i bs'
              return i'
      else return i

instance Unique SortedReft where
  uniq (RR s r) = RR s <$> uniq r

instance Unique Reft where
  uniq (Reft (x,e)) = (Reft . (x,)) <$> uniq e

instance Unique Expr where
  uniq = mapMExpr go
   where
    go (PGrad k su i e) = do
      k'  <- freshK k
      src <- uloc <$> get
      return $ PGrad k' su (i{gused = src}) e
    go e              = return e

-------------------------------------------------------------------------------
-- | The Unique Monad ---------------------------------------------------------
-------------------------------------------------------------------------------

type UniqueM = State UniqueST
data UniqueST
  = UniqueST { freshId :: Integer
             , kmap    :: GSpan
             , change  :: Bool
             , cache   :: M.HashMap KVar KVar
             , uloc    :: Maybe SrcSpan
             , ubs     :: [BindId]
             , benv    :: BindEnv
             }



updateLoc :: SrcSpan -> UniqueM ()
updateLoc x = modify $ \s -> s{uloc = Just x}

withCache :: UniqueM a -> UniqueM a
withCache act = do
  emptyCache
  a <- act
  emptyCache
  return a

emptyCache :: UniqueM ()
emptyCache = modify $ \s -> s{cache = mempty}


updateBEnv :: BindId -> BindEnv -> UniqueM ()
updateBEnv i bs = modify $ \s -> s{benv = bs, ubs = i:(ubs s)}

setChange :: UniqueM ()
setChange = modify $ \s -> s{change = True}

resetChange :: UniqueM ()
resetChange = modify $ \s -> s{change = False}

initUniqueST :: BindEnv ->  UniqueST
initUniqueST = UniqueST 0 mempty False mempty Nothing mempty

freshK, freshK', freshK'' :: KVar -> UniqueM KVar
freshK k  = do
  setChange
  cached <- cache <$> get
  case M.lookup k cached of
    {- OPTIMIZATION: Only create one fresh occurence of ? per constraint environment. -}
    Just k' -> return  k'
    Nothing -> freshK'' k

-- M.HashMap KVar [(KVar, Maybe SrcSpan)]

freshK'' k = do 
  curr <- kmap <$> get 
  loc  <- uloc <$> get 
  case M.lookup k curr of 
    Nothing -> freshK' k 
    Just xs -> do spans <- existingSpan k loc xs 
                  case spans of 
                    Just k' -> return k' 
                    Nothing -> freshK' k 


{-
Interesting Relative Positions

           [.......]
Ouside     |  [..]
Inside   [............]
Smaller    [..............] 
Greater      [....]

-}

data RelativePos a
  = Outside  a 
  | Inside   a 
  | Smaller  a 
  | Greater  a
  | NoRelative

existingSpan :: KVar -> Maybe SrcSpan -> [(KVar, Maybe SrcSpan)] -> UniqueM (Maybe KVar)
existingSpan _ Nothing _ = return Nothing 
existingSpan k (Just span) kspans
  = case go kspans of 
      Inside  (k',_)  -> updateK k k' span                 >> (return $ Just k')
      Outside (k',sp) -> updateLoc sp                      >> (return $ Just k')
      Smaller (k',sp) -> updateK k k' (sp `spanDiff` span) >> (return $ Just k')
      Greater (k',sp) -> updateLoc    (sp `spanDiff` span) >> (return $ Just k')
      NoRelative    -> return Nothing

  where
    go []                    = NoRelative
    go ((_,Nothing):sps)     = go sps
    go ((x,Just sp):sps) 
      | span `inSpan` sp    = Inside  (x, sp) 
      | sp `inSpan` span    = Outside (x, sp) 
      | span `isSmaller` sp = Smaller (x, sp)
      | sp `isSmaller` span = Greater (x, sp)
      | otherwise           = go sps 



spanDiff :: SrcSpan -> SrcSpan -> SrcSpan
spanDiff (SS _ end1) (SS _ end2) = SS (toSourcePos (f,l,c-1)) end2
  where (f,l,c) = sourcePosElts end1

inSpan :: SrcSpan -> SrcSpan -> Bool 
inSpan (SS start1 end1) (SS start2 end2) 
  = start1' > start2' && end1' <= end2'
  where
    [start1',start2',end1',end2'] = sourcePosElts <$> [start1,start2,end1,end2]  


isSmaller :: SrcSpan -> SrcSpan -> Bool 
isSmaller (SS start1 end1) (SS start2 end2) 
  = start1' == start2' && end1' <= end2'
  where
    [start1',start2',end1',end2'] = sourcePosElts <$> [start1,start2,end1,end2]  


freshK' k = do
  i <- freshId <$> get
  modify $ (\s -> s{freshId = i + 1})
  let k' = KV $ gradIntSymbol i
  addK k k'
  addCache k k'
  return k'


updateK :: KVar -> KVar -> SrcSpan -> UniqueM ()
updateK k k' sp = 
  modify $ (\s -> s{kmap = M.mapWithKey f (kmap s)})
  where
    f key val 
      | key == k  = (\(kk,vv) -> if kk == k' then (kk,Just sp) else (kk,vv)) <$> val 
      | otherwise = val 

addK :: KVar -> KVar -> UniqueM ()
addK key val =
  modify $ (\s -> s{kmap = M.insertWith (++) key [(val, uloc s)] (kmap s)})

addCache :: KVar -> KVar -> UniqueM ()
addCache k k' = modify $ \s -> s{cache = M.insert k k' (cache s)}

-------------------------------------------------------------------------------
-- | expandWF -----------------------------------------------------------------
-------------------------------------------------------------------------------

expandWF :: (NFData a, Fixpoint a)
         => GSpan
         -> M.HashMap KVar (WfC a)
         -> M.HashMap KVar (WfC a)
expandWF km ws
  = M.fromList $
       ([(k, updateKVar k src w) | (i, w) <- gws, (kw, ks) <- km', kw == i, (k, src) <- ks]
        ++ kws)
  where
    (gws, kws)       = L.partition (isGWfc . snd) $ M.toList ws
    km'              = M.toList km
    updateKVar k src wfc = wfc { wrft = (\(v,s,_) -> (v,s,k)) $ wrft wfc
                               , wloc = (wloc wfc){gused = src}
                               }

