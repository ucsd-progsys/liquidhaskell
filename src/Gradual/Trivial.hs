module Gradual.Trivial (simplify) where

import Language.Fixpoint.Types  hiding (simplify)
import qualified Data.IntMap.Strict       as IntMap


simplify :: SInfo a -> SInfo a 
simplify sinfo = sinfo {cm = IntMap.map f (cm sinfo)}
  where
    f c | PGrad _ _ _ e <- _crhs c 
      = c { _crhs = e} 
    f c = c 
