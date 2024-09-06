{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module GHC.Types_LHAssumptions() where

import GHC.Types

-- This definition is needed to make the listed data constructors
-- visible to LH
_f = (D#, F#, W#)

{-@
//  Boxed types
embed GHC.Types.Double  as real
embed GHC.Prim.Double#  as real
embed GHC.Types.Float   as real
embed GHC.Prim.Float#   as real
embed GHC.Types.Word    as int
embed GHC.Prim.Word#    as int
embed GHC.Prim.Word64#  as int
embed GHC.Types.Int     as int
embed GHC.Prim.Int#     as int
embed GHC.Types.Bool    as bool
embed GHC.Types.Char    as Char
embed GHC.Prim.Char#    as Char
embed GHC.Prim.Addr#    as Str

embed GHC.Num.Integer.Integer as int

assume GHC.Types.True    :: {v:GHC.Types.Bool | v     }
assume GHC.Types.False   :: {v:GHC.Types.Bool | (~ v) }
assume GHC.Types.isTrue# :: n:_ -> {v:GHC.Types.Bool | (n = 1 <=> v)}

assume GHC.Types.D# :: x:GHC.Prim.Double# -> {v: GHC.Types.Double | v = (x :: real) }
assume GHC.Types.F# :: x:GHC.Prim.Float# -> {v: GHC.Types.Float | v = (x :: real) }
assume GHC.Types.I# :: x:GHC.Prim.Int# -> {v: GHC.Types.Int | v = (x :: int) }
assume GHC.Types.C# :: x:GHC.Prim.Char# -> {v: GHC.Types.Char | v = (x :: Char) }
assume GHC.Types.W# :: w:GHC.Prim.Word# -> {v:GHC.Types.Word | v == w }

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
@-}
