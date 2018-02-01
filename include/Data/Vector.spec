module spec Data.Vector where

import GHC.Base

data variance Data.Vector.Vector covariant

measure vlen    :: forall a. (Data.Vector.Vector a) -> Int

invariant       {v: Data.Vector.Vector a | 0 <= vlen v && 0 <= len v }

assume !           :: forall a. x:(Data.Vector.Vector a) -> vec:{ v:Nat | v < vlen x && v < len x } -> a

assume unsafeIndex :: forall a. x:(Data.Vector.Vector a) -> vec:{ v:Nat | v < vlen x && v < len x } -> a

assume fromList    :: forall a. x:[a] -> { v: Data.Vector.Vector a  | vlen v = len x && len v = len x }

assume length      :: forall a. x:(Data.Vector.Vector a) -> { v : Nat | v = vlen x && v = len x }

assume replicate   :: n:Nat -> a -> { v:Data.Vector.Vector a | vlen v = n && len v = n }

assume imap        :: (Nat -> a -> b) -> x:(Data.Vector.Vector a) -> { y:Data.Vector.Vector b | vlen y = vlen x && len y = len x }

assume map         :: (a -> b) -> x:(Data.Vector.Vector a) -> { y:Data.Vector.Vector b | vlen y = vlen x && len y = len x }