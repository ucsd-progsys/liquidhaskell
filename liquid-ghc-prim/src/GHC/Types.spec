module spec GHC.Types where

//  Boxed types
embed GHC.Types.Double  as real
embed GHC.Types.Float   as real
embed GHC.Types.Word    as int
embed GHC.Types.Int     as int
embed GHC.Types.Bool    as bool
embed GHC.Types.Char    as Char

embed GHC.Integer.Type.Integer as int
embed GHC.Num.Integer as int

GHC.Types.True  :: {v:GHC.Types.Bool | v     }
GHC.Types.False :: {v:GHC.Types.Bool | (~ v) }
GHC.Types.isTrue#  :: n:_ -> {v:GHC.Types.Bool | (n = 1 <=> v)}

GHC.Types.D# :: x:GHC.Prim.Double# -> {v: GHC.Types.Double | v = (x :: real) }
GHC.Types.F# :: x:GHC.Prim.Float# -> {v: GHC.Types.Float | v = (x :: real) }
GHC.Types.I# :: x:GHC.Prim.Int# -> {v: GHC.Types.Int | v = (x :: int) }
GHC.Types.C# :: x:GHC.Prim.Char# -> {v: GHC.Types.Char | v = (x :: Char) }
GHC.Types.W# :: w:_ -> {v:GHC.Types.Word | v == w }

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

class measure len :: forall f a. f a -> GHC.Types.Int
