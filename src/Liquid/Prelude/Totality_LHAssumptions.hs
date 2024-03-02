{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Liquid.Prelude.Totality_LHAssumptions where

import Control.Exception.Base

{-@
measure totalityError :: a -> Bool

assume GHC.Internal.Control.Exception.Base.patError :: {v:GHC.Prim.Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a

assume GHC.Internal.Control.Exception.Base.recSelError :: {v:GHC.Prim.Addr# | totalityError "Use of partial record field selector"} -> a

assume GHC.Internal.Control.Exception.Base.nonExhaustiveGuardsError :: {v:GHC.Prim.Addr# | totalityError "Guards are non-exhaustive"} -> a

assume GHC.Internal.Control.Exception.Base.noMethodBindingError :: {v:GHC.Prim.Addr# | totalityError "Missing method(s) on instance declaration"} -> a

assume GHC.Internal.Control.Exception.Base.recConError :: {v:GHC.Prim.Addr# | totalityError "Missing field in record construction"} -> a
@-}
