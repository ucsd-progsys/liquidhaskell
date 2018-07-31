{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE OverloadedStrings     #-}

module Language.Haskell.Liquid.Bare.Expand 
  ( -- * Create alias expansion environment
    makeRTEnv 
    -- * Use alias expansion 
  , Expand (..)
  , expandLoc 

    -- * Expand and Qualify 
  , expandQualify 
  , cookSpecType
  , plugHoles
  ) where

import Prelude hiding (error)
import Data.Graph hiding (Graph)
import Data.Maybe

import qualified Control.Exception         as Ex
import qualified Data.HashMap.Strict       as M
import qualified Data.List                 as L
import qualified Text.Printf               as Printf 
import qualified Text.PrettyPrint.HughesPJ as PJ



import qualified Language.Fixpoint.Types               as F 
import qualified Language.Fixpoint.Misc                as Misc 
import           Language.Fixpoint.Types (Expr(..)) -- , Symbol, symbol) 
import qualified Language.Haskell.Liquid.GHC.Misc      as GM 
import qualified Language.Haskell.Liquid.GHC.API       as Ghc 
import qualified Language.Haskell.Liquid.Types.RefType as RT 
import           Language.Haskell.Liquid.Types

import qualified Language.Haskell.Liquid.Measure      as Ms
import qualified Language.Haskell.Liquid.Bare.Resolve as Bare
import qualified Language.Haskell.Liquid.Bare.Types   as Bare
import qualified Language.Haskell.Liquid.Bare.Plugged as Bare

--------------------------------------------------------------------------------
-- | `makeRTEnv` initializes the env needed to `expand` refinements and types,
--   that is, the below needs to be called *before* we use `Expand.expand`
--------------------------------------------------------------------------------
makeRTEnv :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.ModSpecs -> LogicMap 
          -> BareRTEnv 
--------------------------------------------------------------------------------
makeRTEnv env m lfSpec specs lmap = makeRTAliases tAs (makeREAliases eAs) 
  where
    tAs   = [ t                   | s      <- M.elems specs,  t <- Ms.aliases  s]
    eAs   = [ specREAlias env m e | (m, s) <- M.toList specs, e <- Ms.ealiases s]
         ++ [ specREAlias env m e | e      <- Ms.ealiases lfSpec                ]                        
         ++ [ specREAlias env m e | (_, xl) <- M.toList (lmSymDefs lmap)
                                  , let e = lmapEAlias xl                       ]

makeREAliases :: [Located (RTAlias F.Symbol F.Expr)] -> BareRTEnv 
makeREAliases = graphExpand buildExprEdges f mempty 
  where
    f rtEnv xt = setREAlias rtEnv (expandLoc rtEnv xt)

-- makeRTAliases :: [Located (RTAlias RTyVar SpecType)] -> SpecRTEnv -> SpecRTEnv  
makeRTAliases :: [Located (RTAlias F.Symbol BareType)] -> BareRTEnv -> BareRTEnv  
makeRTAliases lxts rte = graphExpand buildTypeEdges f rte lxts 
  where
    f rtEnv xt         = setRTAlias rtEnv (expandLoc rtEnv xt)

{- 
specRTAlias :: Bare.Env -> ModName -> Located (RTAlias Symbol BareType) -> Located (RTAlias RTyVar SpecType) 
specRTAlias env m la = F.atLoc la $ RTA 
  { rtName  = rtName a
  , rtTArgs = symbolRTyVar <$> rtTArgs a
  , rtVArgs = rtVArgs a 
  , rtBody  = F.val (Bare.ofBareType env m (F.atLoc la (rtBody a))) 
  } 
  where a   = val la 
-}

specREAlias :: Bare.Env -> ModName -> Located (RTAlias F.Symbol F.Expr) -> Located (RTAlias F.Symbol F.Expr) 
specREAlias env m la = F.atLoc la $ a { rtBody = Bare.qualify env m (rtBody a) } 
  where 
    a     = val la 


--------------------------------------------------------------------------------------------------------------

graphExpand :: (PPrint t)
            => (AliasTable x t -> t -> [F.Symbol])         -- ^ dependencies
            -> (thing -> Located (RTAlias x t) -> thing) -- ^ update
            -> thing                                     -- ^ initial
            -> [Located (RTAlias x t)]                   -- ^ vertices
            -> thing                                     -- ^ final 
graphExpand buildEdges expBody env lxts 
           = L.foldl' expBody env (genExpandOrder table' graph)
  where 
    -- xts    = val <$> lxts
    table  = buildAliasTable lxts
    graph  = buildAliasGraph (buildEdges table) lxts
    table' = checkCyclicAliases table graph

setRTAlias :: RTEnv x t -> Located (RTAlias x t) -> RTEnv x t 
setRTAlias env a = env { typeAliases =  M.insert n a (typeAliases env) } 
  where 
    n            = rtName (val a)  

setREAlias :: RTEnv x t -> Located (RTAlias F.Symbol F.Expr) -> RTEnv x t 
setREAlias env a = env { exprAliases = M.insert n a (exprAliases env) } 
  where 
    n            = rtName (val a)



--------------------------------------------------------------------------------
type AliasTable x t = M.HashMap F.Symbol (Located (RTAlias x t))

buildAliasTable :: [Located (RTAlias x t)] -> AliasTable x t
buildAliasTable = M.fromList . map (\rta -> (rtName (val rta), rta))

fromAliasSymbol :: AliasTable x t -> F.Symbol -> Located (RTAlias x t)
fromAliasSymbol table sym
  = fromMaybe err (M.lookup sym table)
  where
    err = panic Nothing $ "fromAliasSymbol: Dangling alias symbol: " ++ show sym

type Graph t = [Node t]
type Node  t = (t, t, [t])

buildAliasGraph :: (PPrint t) => (t -> [F.Symbol]) -> [Located (RTAlias x t)] 
                -> Graph F.Symbol
buildAliasGraph buildEdges = map (buildAliasNode buildEdges)

buildAliasNode :: (PPrint t) => (t -> [F.Symbol]) -> Located (RTAlias x t) 
               -> Node F.Symbol
buildAliasNode f la = (rtName a, rtName a, f (rtBody a))
  where 
    a               = val la 

checkCyclicAliases :: AliasTable x t -> Graph F.Symbol -> AliasTable x t 
checkCyclicAliases table graph
  = case mapMaybe go (stronglyConnComp graph) of
      []   -> table 
      sccs -> Ex.throw (cycleAliasErr table <$> sccs)
    where
      go (CyclicSCC vs) = Just vs
      go (AcyclicSCC _) = Nothing

cycleAliasErr :: AliasTable x t -> [F.Symbol] -> Error
cycleAliasErr _ []          = panic Nothing "checkCyclicAliases: No type aliases in reported cycle"
cycleAliasErr t scc@(rta:_) = ErrAliasCycle { pos    = fst (locate rta)
                                            , acycle = map locate scc }
  where
    locate sym = ( GM.fSrcSpan $ fromAliasSymbol t sym
                 , pprint sym )


genExpandOrder :: AliasTable x t -> Graph F.Symbol -> [Located (RTAlias x t)]
genExpandOrder table graph
  = map (fromAliasSymbol table) symOrder
  where
    (digraph, lookupVertex, _)
      = graphFromEdges graph
    symOrder
      = map (Misc.fst3 . lookupVertex) $ reverse $ topSort digraph

--------------------------------------------------------------------------------

ordNub :: Ord a => [a] -> [a]
ordNub = map head . L.group . L.sort

buildTypeEdges :: (F.Symbolic c) => AliasTable x t -> RType c tv r -> [F.Symbol]
buildTypeEdges table = ordNub . go
  where
    -- go :: t -> [Symbol]
    go (RApp c ts rs _) = go_alias (F.symbol c) ++ concatMap go ts ++ concatMap go (mapMaybe go_ref rs)
    go (RImpF _ t1 t2 _) = go t1 ++ go t2
    go (RFun _ t1 t2 _) = go t1 ++ go t2
    go (RAppTy t1 t2 _) = go t1 ++ go t2
    go (RAllE _ t1 t2)  = go t1 ++ go t2
    go (REx _ t1 t2)    = go t1 ++ go t2
    go (RAllT _ t)      = go t
    go (RAllP _ t)      = go t
    go (RAllS _ t)      = go t
    go (RVar _ _)       = []
    go (RExprArg _)     = []
    go (RHole _)        = []
    go (RRTy env _ _ t) = concatMap (go . snd) env ++ go t
    go_alias c          = [c | M.member c table]
    go_ref (RProp _ (RHole _)) = Nothing
    go_ref (RProp  _ t) = Just t

buildExprEdges :: M.HashMap F.Symbol a -> F.Expr -> [F.Symbol]
buildExprEdges table  = ordNub . go
  where
    go :: F.Expr -> [F.Symbol]
    go (EApp e1 e2)   = go e1 ++ go e2
    go (ENeg e)       = go e
    go (EBin _ e1 e2) = go e1 ++ go e2
    go (EIte _ e1 e2) = go e1 ++ go e2
    go (ECst e _)     = go e
    go (ESym _)       = []
    go (ECon _)       = []
    go (EVar v)       = go_alias v
    go (PAnd ps)       = concatMap go ps
    go (POr ps)        = concatMap go ps
    go (PNot p)        = go p
    go (PImp p q)      = go p ++ go q
    go (PIff p q)      = go p ++ go q
    go (PAll _ p)      = go p
    go (ELam _ e)      = go e
    go (ECoerc _ _ e)  = go e
    go (PAtom _ e1 e2) = go e1 ++ go e2
    go (ETApp e _)     = go e
    go (ETAbs e _)     = go e
    go (PKVar _ _)     = []
    go (PExist _ e)    = go e
    go (PGrad _ _ _ e) = go e
    go_alias f         = [f | M.member f table ]


----------------------------------------------------------------------------------
-- | Using the `SpecRTEnv` to do alias-expansion 
----------------------------------------------------------------------------------
class Expand a where 
  expand :: BareRTEnv -> F.SourcePos -> a -> a 

expandQualify :: (Expand a, Bare.Qualify a) => Bare.Env -> ModName -> BareRTEnv -> F.SourcePos -> a -> a 
expandQualify env name rtEnv l = Bare.qualify env name . expand rtEnv l


----------------------------------------------------------------------------------

expandLoc :: (Expand a) => BareRTEnv -> Located a -> Located a 
expandLoc rtEnv lx = expand rtEnv (F.loc lx) <$> lx 

instance Expand Expr where 
  expand _ _ x = x -- TODO-REBARE 

instance Expand (RTAlias F.Symbol Expr) where 
  expand _ _ x = x -- TODO-REBARE 

instance Expand BareRTAlias where 
  expand _ _ x = x -- TODO-REBARE 

instance Expand BareType where 
  expand = expandBareType 

instance Expand Body where 
  expand rtEnv l (P   p) = P   (expand rtEnv l p) 
  expand rtEnv l (E   e) = E   (expand rtEnv l e)
  expand rtEnv l (R x p) = R x (expand rtEnv l p)


expandBareType :: BareRTEnv -> F.SourcePos -> BareType -> BareType 
expandBareType rtEnv _   = go -- HEREHEREHERE
  where
    go (RApp c ts rs r)  = case lookupRTEnv c rtEnv of 
                             Just rta -> expandRTAliasApp (GM.fSourcePos c) rta (go <$> ts) r 
                             Nothing  -> RApp c (go <$> ts) rs r 
    go (RAppTy t1 t2 r)  = RAppTy (go t1) (go t2) r
    go (RImpF x t1 t2 r) = RImpF x (go t1) (go t2) r 
    go (RFun  x t1 t2 r) = RFun  x (go t1) (go t2) r 
    go (RAllT a t)       = RAllT a (go t) 
    go (RAllP a t)       = RAllP a (go t) 
    go (RAllS x t)       = RAllS x (go t)
    go (RAllE x t1 t2)   = RAllE x (go t1) (go t2)
    go (REx x t1 t2)     = REx   x (go t1) (go t2)
    go (RRTy e r o t)    = RRTy  e r o     (go t)
    go t@(RHole {})      = t 
    go t@(RVar {})       = t 
    go t@(RExprArg {})   = t 

lookupRTEnv :: BTyCon -> BareRTEnv -> Maybe (Located BareRTAlias)
lookupRTEnv c rtEnv = M.lookup (F.symbol c) (typeAliases rtEnv)

expandRTAliasApp :: F.SourcePos -> Located BareRTAlias -> [BareType] -> RReft -> BareType 
expandRTAliasApp l (Loc la _ rta) args r = case isOK of 
  Just e     -> Ex.throw e
  Nothing    -> F.subst esu . (`RT.strengthen` r) . RT.subsTyVars_meet tsu $ rtBody rta
  where
    tsu       = zipWith (\α t -> (α, toRSort t, t)) αs ts
    esu       = F.mkSubst $ zip (F.symbol <$> εs) es
    es        = exprArg l msg <$> es0
    (ts, es0) = splitAt nαs args
    (αs, εs)  = (BTV <$> rtTArgs rta, rtVArgs rta)
    targs     = takeWhile (not . isRExprArg) args
    eargs     = dropWhile (not . isRExprArg) args

    -- ERROR Checking Code
    msg       = "EXPAND-RTALIAS-APP: " ++ F.showpp (rtName rta)
    nαs       = length αs
    nεs       = length εs 
    nargs     = length args 
    ntargs    = length targs
    neargs    = length eargs
    err       = errRTAliasApp l la rta 
    isOK :: Maybe Error
    isOK
      | nargs /= ntargs + neargs
      = err $ PJ.hsep ["Expects", pprint nαs, "type arguments and then", pprint nεs, "expression arguments, but is given", pprint nargs]
      | nargs /= nαs + nεs
      = err $ PJ.hsep ["Expects", pprint nαs, "type arguments and "    , pprint nεs, "expression arguments, but is given", pprint nargs]
      | nαs /= ntargs, not (null eargs)
      = err $ PJ.hsep ["Expects", pprint nαs, "type arguments before expression arguments"]
      | otherwise
      = Nothing

isRExprArg :: RType c tv r -> Bool
isRExprArg (RExprArg _) = True 
isRExprArg _            = False 

errRTAliasApp :: F.SourcePos -> F.SourcePos -> BareRTAlias -> PJ.Doc -> Maybe Error 
errRTAliasApp l la rta = Just . ErrAliasApp  sp name sp' 
  where 
    name            = pprint              (rtName rta)
    sp              = GM.sourcePosSrcSpan l
    sp'             = GM.sourcePosSrcSpan la 



--------------------------------------------------------------------------------
-- | exprArg converts a tyVar to an exprVar because parser cannot tell
--   this function allows us to treating (parsed) "types" as "value"
--   arguments, e.g. type Matrix a Row Col = List (List a Row) Col
--   Note that during parsing, we don't necessarily know whether a
--   string is a type or a value expression. E.g. in tests/pos/T1189.hs,
--   the string `Prop (Ev (plus n n))` where `Prop` is the alias:
--     {-@ type Prop E = {v:_ | prop v = E} @-}
--   the parser will chomp in `Ev (plus n n)` as a `BareType` and so
--   `exprArg` converts that `BareType` into an `Expr`.
--------------------------------------------------------------------------------
exprArg :: F.SourcePos -> String -> BareType -> Expr
exprArg l msg = go 
  where 
    go :: BareType -> Expr
    go (RExprArg e)     = val e
    go (RVar x _)       = EVar (F.symbol x)
    go (RApp x [] [] _) = EVar (F.symbol x)
    go (RApp f ts [] _) = F.mkEApp (F.symbol <$> btc_tc f) (go <$> ts)
    go (RAppTy t1 t2 _) = F.EApp (go t1) (go t2)
    go z                = panic sp $ Printf.printf "Unexpected expression parameter: %s in %s" (show z) msg
    sp                  = Just (GM.sourcePosSrcSpan l)


----------------------------------------------------------------------------------------
-- | @cookSpecType@ is the central place where a @BareType@ gets processed, 
--   in multiple steps, into a @SpecType@. See [NOTE:Cooking-SpecType] for 
--   details of each of the individual steps.
----------------------------------------------------------------------------------------
cookSpecType :: Bare.Env -> Bare.SigEnv -> ModName -> Maybe Ghc.Var -> LocBareType -> LocSpecType 
----------------------------------------------------------------------------------------
cookSpecType env sigEnv name x
  = id 
  -- TODO-REBARE . strengthenMeasures env sigEnv      x 
  -- TODO-REBARE . strengthenInlines  env sigEnv      x  
  -- TODO-REBARE . fmap fixCoercions
  . fmap RT.generalize
  . maybePlug       sigEnv name x
  . Bare.qualify       env name 
  . bareSpecType       env name 
  . bareExpandType     sigEnv

maybePlug :: Bare.SigEnv -> ModName -> Maybe Ghc.Var -> LocSpecType -> LocSpecType 
maybePlug _      _     Nothing = id 
maybePlug sigEnv name (Just x) = plugHoles sigEnv name x 


bareExpandType :: Bare.SigEnv -> LocBareType -> LocBareType 
bareExpandType sigEnv = expandLoc (Bare.sigRTEnv sigEnv) 

bareSpecType :: Bare.Env -> ModName -> LocBareType -> LocSpecType 
bareSpecType env name lt = Bare.ofBareType env name (F.loc lt) <$> lt

plugHoles :: Bare.SigEnv -> ModName -> Ghc.Var -> LocSpecType -> LocSpecType 
plugHoles sigEnv name = Bare.makePluggedSig name embs tyi exports
  where 
    embs              = Bare.sigEmbs     sigEnv 
    tyi               = Bare.sigTyRTyMap sigEnv 
    exports           = Bare.sigExports  sigEnv 

{- [NOTE:Cooking-SpecType] 
    A @SpecType@ is _raw_ when it is obtained directly from a @BareType@, i.e. 
    just by replacing all the @BTyCon@ with @RTyCon@. Before it can be used 
    for constraint generation, we need to _cook_ it via the following transforms:

    A @SigEnv@ should contain _all_ the information needed to do the below steps.

    - expand               : resolving all type/refinement etc. aliases 
    - ofType               : convert BareType -> SpecType
    - plugged              : filling in any remaining "holes"
    - txRefSort            : filling in the abstract-refinement predicates etc. (YUCK) 
    - resolve              : renaming / qualifying symbols?
    - generalize           : (universally) quantify free type variables 
    - strengthen-measures  : ?
    - strengthen-inline(?) : ? 

-}

