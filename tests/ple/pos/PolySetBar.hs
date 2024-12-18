{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module PolySetBar where

import Prelude hiding (last)
import Data.Set
import PolySetFoo

{-@ lemma_last_isFoo :: f : Foo t -> { isFoo (last (foos f))} @-}
lemma_last_isFoo :: Foo t -> ()
lemma_last_isFoo f = if isFoo f then () else ()
