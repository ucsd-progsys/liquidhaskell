{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Liquid.Prelude.Totality_LHAssumptions where

import Control.Exception.Base
import GHC.Prim

{-@
measure totalityError :: a -> Bool

assume GHC.Internal.Control.Exception.Base.patError :: {v:Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a

assume GHC.Internal.Control.Exception.Base.recSelError :: {v:Addr# | totalityError "Use of partial record field selector"} -> a

assume GHC.Internal.Control.Exception.Base.nonExhaustiveGuardsError :: {v:Addr# | totalityError "Guards are non-exhaustive"} -> a

assume GHC.Internal.Control.Exception.Base.noMethodBindingError :: {v:Addr# | totalityError "Missing method(s) on instance declaration"} -> a

assume GHC.Internal.Control.Exception.Base.recConError :: {v:Addr# | totalityError "Missing field in record construction"} -> a
@-}
