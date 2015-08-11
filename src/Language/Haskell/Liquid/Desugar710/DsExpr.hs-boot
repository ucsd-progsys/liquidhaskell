module Language.Haskell.Liquid.Desugar710.DsExpr where
import HsSyn    ( HsExpr, LHsExpr, HsLocalBinds )
import Var      ( Id )
import DsMonad  ( DsM )
import CoreSyn  ( CoreExpr )

dsExpr  :: HsExpr  Id -> DsM CoreExpr
dsLExpr :: LHsExpr Id -> DsM CoreExpr
dsLocalBinds :: HsLocalBinds Id -> CoreExpr -> DsM CoreExpr
