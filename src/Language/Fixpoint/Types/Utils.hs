-- | This module has various utility functions for accessing queries.
--   TODO: move the "clients" in Visitors into this module.

module Language.Fixpoint.Types.Utils (
  -- * Domain of a kvar
    kvarDomain

  -- * Free variables in a refinement
  , reftFreeVars

  -- * Deconstruct a SortedReft
  , sortedReftConcKVars

  -- * Operators on DataDecl
  , checkRegular
  , orderDeclarations

  ) where

import qualified Data.HashMap.Strict                  as M
import qualified Data.HashSet                         as S

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Types.Sorts
import qualified Language.Fixpoint.Misc as Misc

--------------------------------------------------------------------------------
-- | Compute the domain of a kvar
--------------------------------------------------------------------------------
kvarDomain :: SInfo a -> KVar -> [Symbol]
--------------------------------------------------------------------------------
kvarDomain si k = domain (bs si) (getWfC si k)

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = fst3 (wrft wfc) : map fst (envCs be $ wenv wfc)

getWfC :: SInfo a -> KVar -> WfC a
getWfC si k = ws si M.! k

--------------------------------------------------------------------------------
-- | Free variables of a refinement
--------------------------------------------------------------------------------
--TODO deduplicate (also in Solver/UniqifyBinds)
reftFreeVars :: Reft -> S.HashSet Symbol
reftFreeVars r@(Reft (v, _)) = S.delete v $ S.fromList $ syms r

--------------------------------------------------------------------------------
-- | Split a SortedReft into its concrete and KVar components
--------------------------------------------------------------------------------
sortedReftConcKVars :: Symbol -> SortedReft -> ([Pred], [KVSub], [KVSub])
sortedReftConcKVars x sr = go [] [] [] ves
  where
    ves                  = [(v, p `subst1` (v, eVar x)) | Reft (v, p) <- rs ]
    rs                   = reftConjuncts (sr_reft sr)
    t                    = sr_sort sr

    go ps ks gs ((v, PKVar k su    ):xs) = go ps (KVS v t k su:ks) gs xs 
    go ps ks gs ((v, PGrad k su _ _):xs) = go ps ks (KVS v t k su:gs) xs 
    go ps ks gs ((_, p):xs)              = go (p:ps) ks gs xs 
    go ps ks gs []                       = (ps, ks, gs)


-------------------------------------------------------------------------------
-- | @checkRegular ds@ returns the subset of ds that are _not_ regular
-------------------------------------------------------------------------------
checkRegular :: [DataDecl] -> [DataDecl]
-------------------------------------------------------------------------------
checkRegular ds = concat [ ds' | ds' <- orderDeclarations ds, not (isRegular ds')]

-------------------------------------------------------------------------------
-- | @isRegular [d1,...]@ gets a non-empty list of mut-recursive datadecls
-------------------------------------------------------------------------------
isRegular :: [DataDecl] -> Bool
-------------------------------------------------------------------------------

isRegular []       = error "impossible: isRegular"
isRegular ds@(d:_) = all (\d' -> ddVars d' == nArgs) ds   -- same number of tyArgs 
                  && all isRegApp fldSortApps         -- 'regular' application (tc @0 ... @n)
  where
    nArgs          = ddVars d
    tcs            = S.fromList ( symbol . ddTyCon <$> ds)
    fldSortApps    = [ (c,ts) | d           <- ds
                              , ctor        <- ddCtors d
                              , DField _ t  <- dcFields ctor 
                              , (c, ts)     <- sortApps t
                     ]         
    isRegApp cts   = case cts of 
                        (FTC c, ts) -> not (S.member (symbol c) tcs) || isRegularArgs nArgs ts
                        _           -> False

isRegularArgs :: Int -> [Sort] -> Bool
isRegularArgs n ts = ts == [FVar i | i <- [0 .. (n-1)]]

type SortApp = (Sort, [Sort])

sortApps :: Sort -> [SortApp]
sortApps = go 
  where 
    go t@FApp {}     = (f, ts) : concatMap go ts where (f, ts) = splitApp t
    go (FFunc t1 t2) = go t1 ++ go t2
    go (FAbs _ t)    = go t
    go _             = []

splitApp :: Sort -> SortApp 
splitApp = go []
  where
    go stk (FApp t1 t2) = go (t2:stk) t1  
    go stk t            = (t, stk)

--------------------------------------------------------------------------------
-- | 'orderDeclarations' sorts the data declarations such that each declarations
--   only refers to preceding ones.
--------------------------------------------------------------------------------
orderDeclarations :: [DataDecl] -> [[DataDecl]]
--------------------------------------------------------------------------------
orderDeclarations ds = {- reverse -} Misc.sccsWith f ds
  where
    dM               = M.fromList [(ddTyCon d, d) | d <- ds]
    f d              = (ddTyCon d, dataDeclDeps dM d)

dataDeclDeps :: M.HashMap FTycon DataDecl -> DataDecl -> [FTycon]
dataDeclDeps dM = filter (`M.member` dM) . Misc.sortNub . dataDeclFTycons

dataDeclFTycons :: DataDecl -> [FTycon]
dataDeclFTycons = concatMap dataCtorFTycons . ddCtors

dataCtorFTycons :: DataCtor -> [FTycon]
dataCtorFTycons = concatMap dataFieldFTycons . dcFields

dataFieldFTycons :: DataField -> [FTycon]
dataFieldFTycons = sortFTycons . dfSort

sortFTycons :: Sort -> [FTycon]
sortFTycons = go
  where
    go (FTC c)       = [c]
    go (FApp  t1 t2) = go t1 ++ go t2
    go (FFunc t1 t2) = go t1 ++ go t2
    go (FAbs _ t)    = go t 
    go _             = []