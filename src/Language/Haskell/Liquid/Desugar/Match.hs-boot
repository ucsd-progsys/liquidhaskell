module Language.Haskell.Liquid.Desugar.Match where
import Var      ( Id )
import TcType   ( Type )
import Language.Haskell.Liquid.Desugar.DsMonad  ( DsM, EquationInfo, MatchResult )
import CoreSyn  ( CoreExpr )
import HsSyn    ( LPat, HsMatchContext, MatchGroup, LHsExpr )
import Name     ( Name )

match   :: [Id]
        -> Type
        -> [EquationInfo]
        -> DsM MatchResult

matchWrapper
        :: HsMatchContext Name
        -> Maybe (LHsExpr Id)
        -> MatchGroup Id (LHsExpr Id)
        -> DsM ([Id], CoreExpr)

matchSimply
        :: CoreExpr
        -> HsMatchContext Name
        -> LPat Id
        -> CoreExpr
        -> CoreExpr
        -> DsM CoreExpr

matchSinglePat
        :: CoreExpr
        -> HsMatchContext Name
        -> LPat Id
        -> Type
        -> MatchResult
        -> DsM MatchResult
