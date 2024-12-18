{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Types_LHAssumptions() where

import GHC.Prim
import GHC.Types

-- This definition is needed to make the listed data constructors
-- visible to LH
_f = (D#, F#, W#)

{-@
//  Boxed types
embed Double  as real
embed Double#  as real
embed Float   as real
embed Float#   as real
embed Word    as int
embed Word#    as int
embed Word64#  as int
embed Int     as int
embed Int#     as int
embed Bool    as bool
embed Char    as Char
embed Char#    as Char
embed Addr#    as Str

embed Integer as int

assume True    :: {v:Bool | v     }
assume False   :: {v:Bool | (~ v) }
assume GHC.Types.isTrue# :: n:_ -> {v:Bool | (n = 1 <=> v)}

assume GHC.Types.D# :: x:Double# -> {v: Double | v = (x :: real) }
assume GHC.Types.F# :: x:Float# -> {v: Float | v = (x :: real) }
assume GHC.Types.I# :: x:Int# -> {v: Int | v = (x :: int) }
assume GHC.Types.C# :: x:Char# -> {v: Char | v = (x :: Char) }
assume GHC.Types.W# :: w:Word# -> {v:Word | v == w }

measure addrLen :: GHC.Prim.Addr# -> Int

type GeInt N = {v: Int | v >= N }
type LeInt N = {v: Int | v <= N }
type Nat     = {v: Int | v >= 0 }
type Even    = {v: Int | (v mod 2) = 0 }
type Odd     = {v: Int | (v mod 2) = 1 }
type BNat N  = {v: Nat           | v <= N }
type TT      = {v: Bool | v}
type FF      = {v: Bool | not v}
type String  = [Char]

class measure len :: forall f a. f a -> Int
@-}
