{--! run liquid with no-termination -}

module Intro where

import Language.Haskell.Liquid.Prelude  (liquidAssert)

-- doesn't work with WEB demo (just says "ERROR" with no message...
--
{-@ Prelude.head :: {v:[a] | false} -> a @-}

bob z = head z
