module Meas where

import Language.Haskell.Liquid.Prelude

insert key value [] 
  = [(key, value)]
