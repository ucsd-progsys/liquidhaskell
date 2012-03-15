module spec Language.Haskell.Liquid.Prelude where

assume plus  :: x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}
assume minus :: x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x - y}
assume times :: x:Int -> y:Int -> Int

assume eq    :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x = y)}
assume neq   :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x != y)}
assume leq   :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x <= y)}
assume geq   :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x >= y)}
assume lt    :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x < y)}
assume gt    :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x > y)}

assume assert :: x:{v:Bool | (? v)} -> {v: Bool | (? v)}
assume crash  :: forall a . x:{v:Bool | (? v)} -> a
