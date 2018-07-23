module spec GHC.Types where

embed GHC.Prim.Int#     as int
embed GHC.Prim.Addr#    as Str
embed GHC.Prim.Char#    as Char
embed GHC.Types.Double#  as real

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

assume GHC.Types.D# :: x:GHC.Types.Double# -> {v: GHC.Types.Double | v = (x :: real) }
assume GHC.Types.I# :: x:GHC.Prim.Int# -> {v: GHC.Types.Int | v = (x :: int) }
assume GHC.Types.C# :: x:GHC.Prim.Char# -> {v: GHC.Types.Char | v = (x :: Char) }
assume GHC.Types.+#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x + y}
assume GHC.Types.-#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x - y}
assume GHC.Types.==# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x = y}
assume GHC.Types.>=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x >= y}
assume GHC.Types.<=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x <= y}
assume GHC.Types.<#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x < y}
assume GHC.Types.>#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x > y}

measure addrLen :: GHC.Prim.Addr# -> GHC.Types.Int
