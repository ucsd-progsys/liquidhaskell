{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Liquid.Prelude.Totality_LHAssumptions where

import Control.Exception.Base
import GHC.Prim

{-@
measure totalityError :: a -> Bool

assume patError :: {v:Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a

assume recSelError :: {v:Addr# | totalityError "Use of partial record field selector"} -> a

assume nonExhaustiveGuardsError :: {v:Addr# | totalityError "Guards are non-exhaustive"} -> a

assume noMethodBindingError :: {v:Addr# | totalityError "Missing method(s) on instance declaration"} -> a

assume recConError :: {v:Addr# | totalityError "Missing field in record construction"} -> a
@-}
