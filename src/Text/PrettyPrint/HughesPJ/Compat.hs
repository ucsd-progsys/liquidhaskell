module Text.PrettyPrint.HughesPJ.Compat (
    module Text.PrettyPrint.HughesPJ,
    (<->),
    ) where

import Text.PrettyPrint.HughesPJ hiding ((<>), first)
import qualified Text.PrettyPrint.HughesPJ as PP

-- | Also known as '<>' in @pretty@, but that clashes with Semigroup's <>
(<->) :: Doc -> Doc -> Doc
(<->) = (PP.<>)

infixl 6 <->
