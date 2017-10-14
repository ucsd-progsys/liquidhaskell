module LocalLazy (bar) where

import Language.Haskell.Liquid.Prelude

{-@ lazy foo @-}
foo x = foo x


bar = liquidAssertB (inf n > 0)
  where n     = choose 0
       {-@ lazy inf @-}
        inf n = inf n
