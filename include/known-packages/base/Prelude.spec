module spec Prelude where

import GHC.Base
import GHC.Int
import GHC.List
import GHC.Maybe
import GHC.Num
import GHC.Real
import GHC.Word

import Data.Foldable
import Data.Maybe
import Data.Tuple
import GHC.Exts
import Liquid.Prelude.Real
import Liquid.Prelude.Totality


//  GHC.Types.D# :: x:_ -> {v:_ | v = x}

GHC.Err.error :: {v:_ | false} -> a 

// assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> { v:GHC.Integer.Type | v = (x :: int) }

embed Integer           as int

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
