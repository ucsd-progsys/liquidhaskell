module Language.Haskell.Liquid.Desugar710.DsMeta (dsBracket) where

import CoreSyn
import DsMonad
import HsExpr
import Name

dsBracket :: HsBracket Name -> [PendingTcSplice] -> DsM CoreExpr

