{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module Prelude_LHAssumptions where

import GHC.Base_LHAssumptions()
import GHC.Float_LHAssumptions()
import GHC.Maybe_LHAssumptions()
import GHC.Num_LHAssumptions()
import GHC.Num.Integer_LHAssumptions()
import GHC.Num.Integer()
import GHC.Real_LHAssumptions()
import Liquid.Prelude.Real_LHAssumptions()
import Liquid.Prelude.Totality_LHAssumptions()

{-@

assume GHC.Internal.Err.error :: {v:_ | false} -> a

predicate Max V X Y = if X > Y then V = X else V = Y
predicate Min V X Y = if X < Y then V = X else V = Y

type IncrListD a  = [a]<{\x y -> (x+D) <= y}>

// BOT: Do not delete EVER!

qualif Bot(v:@(0))    : (0 = 1)
qualif Bot(v:obj)     : (0 = 1)
qualif Bot(v:a)       : (0 = 1)
qualif Bot(v:bool)    : (0 = 1)
qualif Bot(v:int)     : (0 = 1)

qualif CmpZ(v:a)      : (v <  0)
qualif CmpZ(v:a)      : (v <= 0)
qualif CmpZ(v:a)      : (v >  0)
qualif CmpZ(v:a)      : (v >= 0)
qualif CmpZ(v:a)      : (v  = 0)
qualif CmpZ(v:a)      : (v != 0)

qualif Cmp(v:a, x:a)  : (v <  x)
qualif Cmp(v:a, x:a)  : (v <= x)
qualif Cmp(v:a, x:a)  : (v >  x)
qualif Cmp(v:a, x:a)  : (v >= x)
qualif Cmp(v:a, x:a)  : (v  = x)
qualif Cmp(v:a, x:a)  : (v != x)

qualif One(v:int)     : v = 1
qualif True1(v:GHC.Types.Bool)   : (v)
qualif False1(v:GHC.Types.Bool)  : (~ v)

//  REBARE constant papp1 : func(1, [Pred @(0); @(0); bool])
qualif Papp(v:a, p:Pred a) : (papp1 p v)

//  REBARE constant papp2 : func(4, [Pred @(0) @(1); @(2); @(3); bool])
qualif Papp2(v:a, x:b, p:Pred a b) : (papp2 p v x)

//  REBARE constant papp3 : func(6, [Pred @(0) @(1) @(2); @(3); @(4); @(5); bool])
qualif Papp3(v:a, x:b, y:c, p:Pred a b c) : (papp3 p v x y)

//  qualif Papp4(v:a,x:b, y:c, z:d, p:Pred a b c d) : papp4(p, v, x, y, z)
//  REBARE constant papp4 : func(8, [Pred @(0) @(1) @(2) @(6); @(3); @(4); @(5); @(7); bool])

//  REBARE constant runFun : func(2, [Arrow @(0) @(1); @(0); @(1)])
@-}
