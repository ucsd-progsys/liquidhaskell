-- | This module defines code for generating termination constraints.

module Language.Haskell.Liquid.Constraint.Termination (
  TCheck(..)
, mkTCheck
, doTermCheck
, makeTermEnvs
, makeDecrIndex
, checkIndex
, recType
, unOCons
) where

import Data.Maybe ( fromJust )
import qualified Data.List                                     as L
import qualified Data.HashSet                                  as S
import Control.Applicative (liftA2)
import Control.Monad.State ( gets )
import Text.PrettyPrint.HughesPJ ( (<+>), text )
import GHC.Types.Var (Var)
import GHC.Types.Name (NamedThing, getSrcSpan)
import GHC.Core.TyCon (TyCon)
import GHC.Core (Bind, CoreExpr, bindersOf)
import qualified Language.Fixpoint.Types                       as F
import Language.Fixpoint.Types.PrettyPrint (PPrint)
import qualified Liquid.GHC.Misc as GM
import Language.Haskell.Liquid.Types.Types
  (SpecType, TError (..), RType (..), RTypeRep (..), Oblig (..), Error, Config (..), RReft,
   toRTypeRep, structuralTerm, bkArrowDeep, mkArrow, bkUniv, bkArrow, fromRTypeRep)
import Language.Haskell.Liquid.Constraint.Types (CG, CGInfo (..), CGEnv)
import Language.Haskell.Liquid.Constraint.Monad (addWarning)
import Language.Haskell.Liquid.Transforms.Rec (isIdTRecBound)
import Language.Haskell.Liquid.Constraint.Env (setTRec)
import Language.Haskell.Liquid.Constraint.Template ( Template(..), unTemplate )
import Language.Haskell.Liquid.Types.RefType (isDecreasing, makeDecrType, makeLexRefa, makeNumEnv)
import Language.Haskell.Liquid.Misc (safeFromLeft, replaceN, (<->), zip4, safeFromJust, fst5)

data TCheck = TerminationCheck | StrataCheck | NoCheck

mkTCheck :: Bool -> Bool -> TCheck
mkTCheck tc is
  | not is    = StrataCheck
  | tc        = TerminationCheck
  | otherwise = NoCheck

doTermCheck :: Config -> Bind Var -> CG Bool
doTermCheck cfg bind = do
  lazyVs    <- gets specLazy
  termVs    <- gets specTmVars
  let skip   = any (\x -> S.member x lazyVs || nocheck x) xs
  let chk    = not (structuralTerm cfg) || any (`S.member` termVs) xs
  return     $ chk && not skip
  where
    nocheck  = if typeclass cfg then GM.isEmbeddedDictVar else GM.isInternal
    xs       = bindersOf bind

makeTermEnvs :: CGEnv -> [(Var, [F.Located F.Expr])] -> [(Var, CoreExpr)]
             -> [SpecType] -> [SpecType]
             -> [CGEnv]
makeTermEnvs γ xtes xes ts ts' = setTRec γ . zip xs <$> rts
  where
    vs   = zipWith collectArgs' ts ces
    syms = fst5 . bkArrowDeep <$> ts
    syms' = fst5 . bkArrowDeep <$> ts'
    sus' = zipWith mkSub syms syms'
    sus  = zipWith mkSub syms ((F.symbol <$>) <$> vs)
    ess  = (\x -> safeFromJust (err x) (x `L.lookup` xtes)) <$> xs
    tes  = zipWith (\su es -> F.subst su <$> es)  sus ess
    tes' = zipWith (\su es -> F.subst su <$> es)  sus' ess
    rss  = zipWith makeLexRefa tes' <$> (repeat <$> tes)
    rts  = zipWith (addObligation OTerm) ts' <$> rss
    (xs, ces)    = unzip xes
    mkSub ys ys' = F.mkSubst [(x, F.EVar y) | (x, y) <- zip ys ys']
    collectArgs' = GM.collectArguments . length . ty_binds . toRTypeRep
    err x        = "Constant: makeTermEnvs: no terminating expression for " ++ GM.showPpr x

addObligation :: Oblig -> SpecType -> RReft -> SpecType
addObligation o t r  = mkArrow αs πs xts $ RRTy [] r o t2
  where
    (αs, πs, t1) = bkUniv t
    ((xs, is, ts, rs), t2) = bkArrow t1
    xts              = zip4 xs is ts rs

--------------------------------------------------------------------------------
-- | TERMINATION TYPE ----------------------------------------------------------
--------------------------------------------------------------------------------

makeDecrIndex :: (Var, Template SpecType, [Var]) -> CG (Maybe Int)
makeDecrIndex (x, Assumed t, args)
  = do dindex <- makeDecrIndexTy x t args
       case dindex of
         Left msg -> addWarning msg >> return Nothing
         Right i -> return $ Just i
makeDecrIndex (x, Asserted t, args)
  = do dindex <- makeDecrIndexTy x t args
       case dindex of
         Left msg -> addWarning msg >> return Nothing
         Right i  -> return $ Just i
makeDecrIndex _ = return Nothing

makeDecrIndexTy :: Var -> SpecType -> [Var] -> CG (Either (TError t) Int)
makeDecrIndexTy x st args
  = do autosz <- gets autoSize
       return $ case dindex autosz of
         Nothing -> Left msg
         Just i  -> Right i
    where
       msg  = ErrTermin (getSrcSpan x) [F.pprint x] (text "No decreasing parameter")
       trep = toRTypeRep $ unOCons st
       ts   = ty_args trep
       tvs  = zip ts args
       cenv = makeNumEnv ts

       p autosz (t, v)   = isDecreasing autosz cenv t && not (isIdTRecBound v)
       dindex     autosz = L.findIndex (p autosz) tvs

recType :: F.Symbolic a
        => S.HashSet TyCon
        -> (([a], Maybe Int), (t, Maybe Int, SpecType))
        -> SpecType
recType _       ((_, Nothing), (_, Nothing, t)) = t
recType autoenv ((vs, indexc), (_, index, t))
  = makeRecType autoenv t v dxt index
  where v    = (vs !!)  <$> indexc
        dxt  = (xts !!) <$> index
        xts  = zip (ty_binds trep) (ty_args trep)
        trep = toRTypeRep $ unOCons t

checkIndex :: (NamedThing t, PPrint t, PPrint a)
           => (t, [a], Template (RType c tv r), Maybe Int)
           -> CG (Maybe (RType c tv r))
checkIndex (_,  _, _, Nothing   ) = return Nothing
checkIndex (x, vs, t, Just index) = safeLogIndex msg1 vs index >> safeLogIndex msg2 ts index
    where
       loc   = getSrcSpan x
       ts    = ty_args $ toRTypeRep $ unOCons $ unTemplate t
       msg1  = ErrTermin loc [xd] (text "No decreasing" <+> F.pprint index <-> text "-th argument on" <+> xd <+> text "with" <+> F.pprint vs)
       msg2  = ErrTermin loc [xd] (text  "No decreasing parameter")
       xd    = F.pprint x

makeRecType :: (Enum a1, Eq a1, Num a1, F.Symbolic a)
            => S.HashSet TyCon
            -> SpecType
            -> Maybe a
            -> Maybe (F.Symbol, SpecType)
            -> Maybe a1
            -> SpecType
makeRecType autoenv t vs dxs is
  = mergecondition t $ fromRTypeRep $ trep {ty_binds = xs', ty_args = ts'}
  where
    (xs', ts') = unzip $ replaceN (fromJust is) (safeFromLeft "makeRecType" $ makeDecrType autoenv vdxs) xts
    vdxs       = liftA2 (,) vs dxs
    xts        = zip (ty_binds trep) (ty_args trep)
    trep       = toRTypeRep $ unOCons t

unOCons :: RType c tv r -> RType c tv r
unOCons (RAllT v t r)      = RAllT v (unOCons t) r
unOCons (RAllP p t)        = RAllP p $ unOCons t
unOCons (RFun x i tx t r)  = RFun x i (unOCons tx) (unOCons t) r
unOCons (RRTy _ _ OCons t) = unOCons t
unOCons t                  = t

mergecondition :: RType c tv r -> RType c tv r -> RType c tv r
mergecondition (RAllT _ t1 _)       (RAllT v t2 r2)        = RAllT v (mergecondition t1 t2) r2
mergecondition (RAllP _ t1)         (RAllP p t2)           = RAllP p (mergecondition t1 t2)
mergecondition (RRTy xts r OCons t1) t2                    = RRTy xts r OCons (mergecondition t1 t2)
mergecondition (RFun _ _ t11 t12 _) (RFun x2 i t21 t22 r2) = RFun x2 i (mergecondition t11 t21) (mergecondition t12 t22) r2
mergecondition _                     t                     = t

safeLogIndex :: Error -> [a] -> Int -> CG (Maybe a)
safeLogIndex err ls n
  | n >= length ls = addWarning err >> return Nothing
  | otherwise      = return $ Just $ ls !! n