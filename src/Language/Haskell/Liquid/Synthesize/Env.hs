module Language.Haskell.Liquid.Synthesize.Env where 

import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Synthesize.Monad

import qualified Data.HashMap.Strict           as M
import qualified Data.HashSet                  as S
import           DataCon
import           TyCon
import           Var

initSSEnv :: SpecType -> CGInfo -> SSEnv -> (SSEnv, [Var])
initSSEnv rt info senv = (M.union senv (M.fromList foralls), vs)
  where
    foralls = filter iNeedIt (mkElem <$> prims)
    vs = map (snd . snd) foralls
    dataCons = typeToCons rt 
    mkElem (v, lt) = (symbol v, (val lt, v))
    prims = gsCtors $ gsData $ giSpec $ ghcI info
    iNeedIt (_, (_, v)) = v `elem` (dataConWorkId <$> dataCons)

-- | For algebraic datatypes: Find (in the refinement type) 
--   all the datatypes that are used and 
--   get their constructors.
tpToCons :: SpecType -> [DataCon] 
tpToCons (RAllT a t x)  
  = tpToCons t 
tpToCons (RApp c args _ r) 
  = tyConDataCons (rtc_tc c) ++ concatMap tpToCons args
tpToCons (RFun sym rt0 rt1 reft)
  = tpToCons rt0 ++ tpToCons rt1
tpToCons (RVar v r) 
  = []
tpToCons (RAllP _ t)
  = tpToCons t
tpToCons (RRTy _ _ _ t)
  = tpToCons t
tpToCons rt 
  = []

typeToCons :: SpecType -> [DataCon]
typeToCons rt = S.toList $ S.fromList (tpToCons rt)
