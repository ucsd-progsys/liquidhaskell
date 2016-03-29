-- ISSUE: this "crashes" without a decent source location
-- You can fix this with the signature `ide :: forall <p :: a -> Prop>. a<p> -> a<p>`
-- but it would be nice to have an error message that pinpoints the location.

module Ide where

{-@ ide :: a<p> -> a<p> @-}
ide x = x
