module Foo () where

import Data.Maybe


foo :: Maybe a -> a
foo x = fromJust x
