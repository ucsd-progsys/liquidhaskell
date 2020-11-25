module Liquid.Prelude.Totality (module Exports) where

import GHC.Types
import "base" Control.Exception.Base as Exports


totalityError :: a -> Bool
totalityError _ = False
