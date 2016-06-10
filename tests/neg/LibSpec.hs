module LibSpec ( module Lib ) where 

import Lib

{-@ Lib.foo :: {v:a | false} -> a @-}

