{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Haskell.Liquid.Transforms.Rec (
     transformRecExpr
     ) where

import           Liquid.GHC.API      as Ghc hiding (panic)
import           Language.Fixpoint.Misc               (mapSnd) -- , traceShow)
import           Language.Haskell.Liquid.Types.Errors
import           Prelude                              hiding (error)

import qualified Data.List                            as L


transformRecExpr :: CoreProgram -> CoreProgram
transformRecExpr = inlineFailCases

-- | Inlines bindings of the form
--
-- > let v = \x -> e0
-- >  in e1
--
-- whenever all of the following hold:
--  * "fail" is a prefix of variable @v@,
--  * @x@ is not free in @e0@, and
--  * v is applied to some value in @e1@.
--
-- In addition to inlining, this function also beta reduces
-- the resulting expressions @(\x -> e0) a@ by replacing them
-- with @e0@.
--
inlineFailCases :: CoreProgram -> CoreProgram
inlineFailCases = (go [] <$>)
  where
    go su (Rec xes)    = Rec (mapSnd (go' su) <$> xes)
    go su (NonRec x e) = NonRec x (go' su e)

    go' su (App (Var x) _)       | isFailId x, Just e <- getFailExpr x su = e
    go' su (Let (NonRec x ex) e) | isFailId x   = go' (addFailExpr x (go' su ex) su) e

    go' su (App e1 e2)      = App (go' su e1) (go' su e2)
    go' su (Lam x e)        = Lam x (go' su e)
    go' su (Let xs e)       = Let (go su xs) (go' su e)
    go' su (Case e x t alt) = Case (go' su e) x t (goalt su <$> alt)
    go' su (Cast e c)       = Cast (go' su e) c
    go' su (Tick t e)       = Tick t (go' su e)
    go' _  e                = e

    goalt su (Alt c xs e)   = Alt c xs (go' su e)

    isFailId x  = isLocalId x && isSystemName (varName x) && L.isPrefixOf "fail" (getOccString x)
    getFailExpr = L.lookup

    addFailExpr x (Lam v e) su
      | not (elemVarSet v $ exprFreeVars e)  = (x, e):su
    addFailExpr _ _         _  = impossible Nothing "internal error" -- this cannot happen

