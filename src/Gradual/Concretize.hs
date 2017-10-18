{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}

module Gradual.Concretize (Gradual(..)) where

import Gradual.Types 
import Language.Fixpoint.Types
import Gradual.Misc

import qualified Data.HashMap.Strict       as M
-- import Debug.Trace 

class Gradual i a where
  concretize :: GMap i -> a -> [a]
  concretize _ x = [x]

instance Gradual i Expr where
  concretize i (PGrad k su _ _) = subst su <$> (snd $ M.lookupDefault err k i) 
    where
      err = (undefined, [PTrue]) -- error ("Gradual Not found: " ++ show k)
  concretize i (PAnd ps) = PAnd <$> expand (concretize i) ps 
  concretize _ p = [p]

instance  Fixpoint a => Gradual i (SInfo a) where
  concretize i sinfo = (\su -> 
     sinfo {bs = gsubst su (bs sinfo), cm = gsubst su (cm sinfo)} 
    ) <$> (M.fromList <$> flatten (M.toList i))

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



class GSubable a where
  gsubst :: GSub -> a -> a 
  gsubst _ x = x 

instance GSubable Expr where
  gsubst i (PGrad k su _ _) = subst su $ M.lookupDefault err k i
    where
      err = PTrue -- error ("Gradual Not found: " ++ show k)
  gsubst i (PAnd ps) = PAnd $ map (gsubst i) ps 
  gsubst _ p = p

instance GSubable BindEnv where
  gsubst i benv = bindEnvFromList (mapThd3 (gsubst i) <$> bindEnvToList benv)

instance GSubable (SimpC a) where
  gsubst i c = c{_crhs = gsubst i (_crhs c)}

instance (GSubable v) => GSubable (M.HashMap SubcId v) where
  gsubst i m = M.map (gsubst i) m

instance GSubable SortedReft where
  gsubst i (RR s r) = RR s $ gsubst i r 

instance GSubable Reft where
  gsubst i (Reft (x,e)) = (Reft . (x,)) $ gsubst i e  
