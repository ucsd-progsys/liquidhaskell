{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TupleSections         #-}

module Gradual.Concretize (Gradual(..)) where

import Gradual.Types 
import Language.Fixpoint.Types
import Gradual.Misc

import qualified Data.HashMap.Strict       as M
-- import Debug.Trace 

class Gradual a where
  concretize :: GMap GWInfo -> a -> [(GSub GWInfo, a)]
  concretize _ x = [(mempty, x)]

instance Gradual (SInfo a) where
  concretize i sinfo = (\su -> (su,
     sinfo {bs = gsubst (bs sinfo,su) (bs sinfo), cm = gsubst (bs sinfo,su) (cm sinfo)} 
    )) <$> (M.fromList <$> flatten (M.toList i))


class GSubable a where
  gsubst :: (BindEnv, GSub GWInfo) -> a -> a 
  gsubst _ x = x 

instance GSubable BindEnv where
  gsubst i benv = bindEnvFromList (mapThd3 (gsubst i) <$> bindEnvToList benv)

instance GSubable (SimpC a) where
  gsubst (benv,i) c = c {_crhs = substGrad x i (_crhs c)}
    where
      x = fst $ lookupBindEnv (_cbind c) benv

instance (GSubable v) => GSubable (M.HashMap SubcId v) where
  gsubst i m = M.map (gsubst i) m

instance GSubable SortedReft where
  gsubst i (RR s r) = RR s $ gsubst i r 

instance GSubable Reft where
  gsubst (_,i) (Reft (x,p)) = Reft . (x,) $ substGrad x i p

-- instance GSubable Expr where
--   gsubst i p = substGrad dummySymbol i p

substGrad :: Symbol -> GSub GWInfo -> Expr -> Expr
substGrad x m (PGrad k su _ e) 
  = case M.lookup k m of 
      Just (i, ek) -> pAnd [subst su $ subst1 ek (gsym i, EVar x), e] 
                      -- in trace ("SUBSTITUTED: STATIC = " ++ showFix e ++ 
                      --           "\t GRADUAL = " ++ showFix ee ++
                      --           "\t INIT = " ++ showFix ek) ee
      Nothing      -> PTrue  
substGrad x m (PAnd es)        
  = PAnd (substGrad x m <$> es)
substGrad _ _ e
  = e 


{- 
instance Gradual i Expr where
  concretize i (PGrad k su _ _) = subst su <$> (snd $ M.lookupDefault err k i) 
    where
      err = (undefined, [PTrue]) -- error ("Gradual Not found: " ++ show k)
  concretize i (PAnd ps) = PAnd <$> expand (concretize i) ps 
  concretize _ p = [p]


instance Gradual i BindEnv where
  concretize i benv = bindEnvFromList <$> expand3 (concretize i) (bindEnvToList benv)

instance Fixpoint a => Gradual i (SimpC a) where
  concretize i c = [c{_crhs = rhs} | rhs <- concretize i (_crhs c)]

instance (Gradual i v) => Gradual i (M.HashMap SubcId v) where
  concretize i m = M.fromList <$> expand2 (concretize i) (M.toList m)

instance Gradual i SortedReft where
  concretize i (RR s r) = RR s <$> concretize i r 

instance Gradual i Reft where
  concretize i (Reft (x,e)) = (Reft . (x,)) <$> concretize i e  
-}
