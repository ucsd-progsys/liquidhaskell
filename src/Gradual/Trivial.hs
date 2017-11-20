module Gradual.Trivial (simplify) where

import Language.Fixpoint.Types  hiding (simplify)
import qualified Data.HashMap.Strict       as M


simplify :: SInfo a -> SInfo a 
simplify sinfo = sinfo {cm = M.map f (cm sinfo)}
  where
    f c | PGrad _ _ _ e <- _crhs c 
      = c { _crhs = e} 
    f c = c 
