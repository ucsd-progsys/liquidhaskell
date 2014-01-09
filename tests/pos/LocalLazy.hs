module LocalLazy () where

import Language.Haskell.Liquid.Prelude

{-@ Lazy foo @-}
foo x = foo x


bar = liquidAssert (inf n > 0)
  where n     = choose 0
       {-@ Lazy inf @-}
        inf n = inf n
