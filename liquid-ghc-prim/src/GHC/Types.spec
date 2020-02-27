module spec GHC.Types where

import GHC.Prim

// Boxed types
embed GHC.Types.Double  as real
embed GHC.Types.Float   as real
embed GHC.Types.Word    as int 
embed GHC.Types.Int     as int
embed GHC.Types.Bool    as bool
embed GHC.Types.Char    as Char

// Prim types
embed GHC.Prim.Int#     as int
embed GHC.Prim.Addr#    as Str
embed GHC.Prim.Char#    as Char
embed GHC.Prim.Double#  as real
embed GHC.Prim.Float#   as real
embed GHC.Prim.Word#    as int

GHC.Types.True  :: {v:GHC.Types.Bool | v     }
GHC.Types.False :: {v:GHC.Types.Bool | (~ v) }

GHC.Types.isTrue#  :: n:_ -> {v:GHC.Types.Bool | (n = 1 <=> v)}

measure addrLen :: GHC.Prim.Addr# -> GHC.Types.Int

type GeInt N = {v: GHC.Types.Int | v >= N }
type LeInt N = {v: GHC.Types.Int | v <= N }
type Nat     = {v: GHC.Types.Int | v >= 0 }
type Even    = {v: GHC.Types.Int | (v mod 2) = 0 }
type Odd     = {v: GHC.Types.Int | (v mod 2) = 1 }
type BNat N  = {v: Nat           | v <= N }
type TT      = {v: GHC.Types.Bool | v}
type FF      = {v: GHC.Types.Bool | not v}
type String  = [GHC.Types.Char]

assume GHC.Prim.+#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x + y}
assume GHC.Prim.-#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x - y}
assume GHC.Prim.==# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x = y}
assume GHC.Prim.>=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x >= y}
assume GHC.Prim.<=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x <= y}
assume GHC.Prim.<#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x < y}
assume GHC.Prim.>#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:GHC.Prim.Int# | v = 1 <=> x > y}

class measure len :: forall f a. f a -> GHC.Types.Int
