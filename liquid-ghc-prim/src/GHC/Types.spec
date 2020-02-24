module spec GHC.Types where

import GHC.Prim

// Boxed types
embed GHC.Types.Double  as real
embed GHC.Types.Float   as real
embed GHC.Types.Word    as int 
//embed GHC.Types.Int     as int
//embed GHC.Types.Bool    as bool
embed GHC.Types.Char    as Char

// TODO: Drop prefix below
// GHC.Types.EQ :: {v:GHC.Types.Ordering | v = (cmp v) }
// GHC.Types.LT :: {v:GHC.Types.Ordering | v = (cmp v) }
// GHC.Types.GT :: {v:GHC.Types.Ordering | v = (cmp v) }

// measure cmp :: GHC.Types.Ordering -> GHC.Types.Ordering
// cmp GHC.Types.EQ = { v | v = GHC.Types.EQ }
// cmp GHC.Types.LT = { v | v = GHC.Types.LT }
// cmp GHC.Types.GT = { v | v = GHC.Types.GT }


GHC.Types.True  :: {v:GHC.Types.Bool | v     }
GHC.Types.False :: {v:GHC.Types.Bool | (~ v) }

GHC.Types.isTrue#  :: n:_ -> {v:GHC.Types.Bool | (n = 1 <=> v)}

GHC.Types.W# :: w:_ -> {v:GHC.Types.Word | v == w }

GHC.Types.D# :: x:GHC.Prim.Double# -> {v: GHC.Types.Double | v = (x :: real) }
GHC.Types.F# :: x:GHC.Prim.Float# -> {v: GHC.Types.Float | v = (x :: real) }
GHC.Types.I# :: x:GHC.Prim.Int# -> {v: GHC.Types.Int | v = (x :: int) }
GHC.Types.C# :: x:GHC.Prim.Char# -> {v: GHC.Types.Char | v = (x :: Char) }

measure addrLen :: GHC.Prim.Addr# -> GHC.Types.Int

// NOTE(adn) Why do we need this measure here whereas in the original implementation
// this was present directly inside GHC.Base?

class measure len :: forall f a. f a -> GHC.Types.Int
instance measure len :: forall a. [a] -> GHC.Types.Int
len []     = 0
len (y GHC.Types.: ys) = 1 + len ys
