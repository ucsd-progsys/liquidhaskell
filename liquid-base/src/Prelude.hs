{-# LANGUAGE Trustworthy #-}
module Prelude (module Exports) where

import Data.Foldable
import Data.Tuple
import GHC.Base
import GHC.CString
import GHC.Classes
import GHC.Exts
import GHC.Int
import GHC.List
import GHC.Num
import GHC.Real
import GHC.Types
import GHC.Word

-- Liquid \"extra\" modules
import Liquid.Prelude.Totality
import Liquid.Prelude.Real

import "base" Prelude as Exports
