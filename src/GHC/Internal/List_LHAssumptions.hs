{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Internal.List_LHAssumptions where

import GHC.List
import GHC.Types_LHAssumptions()

{-@

assume GHC.Internal.List.head         :: xs:{v: [a] | len v > 0} -> {v:a | v = head xs}
assume GHC.Internal.List.tail         :: xs:{v: [a] | len v > 0} -> {v: [a] | len(v) = (len(xs) - 1) && v = tail xs}

assume GHC.Internal.List.last         :: xs:{v: [a] | len v > 0} -> a
assume GHC.Internal.List.init         :: xs:{v: [a] | len v > 0} -> {v: [a] | len(v) = len(xs) - 1}
assume GHC.Internal.List.null         :: xs:[a] -> {v: GHC.Types.Bool | ((v) <=> len(xs) = 0) }
assume GHC.Internal.List.length       :: xs:[a] -> {v: GHC.Types.Int | v = len(xs)}
assume GHC.Internal.List.filter       :: (a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}
assume GHC.Internal.List.scanl        :: (a -> b -> a) -> a -> xs:[b] -> {v: [a] | len(v) = 1 + len(xs) }
assume GHC.Internal.List.scanl1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) }
assume GHC.Internal.List.foldr1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> a
assume GHC.Internal.List.scanr        :: (a -> b -> b) -> b -> xs:[a] -> {v: [b] | len(v) = 1 + len(xs) }
assume GHC.Internal.List.scanr1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) }

lazy GHC.Internal.List.iterate
assume GHC.Internal.List.iterate :: (a -> a) -> a -> [a]

assume GHC.Internal.List.repeat :: a -> [a]
lazy GHC.Internal.List.repeat

assume GHC.Internal.List.replicate    :: n:Nat -> x:a -> {v: [{v:a | v = x}] | len(v) = n}

assume GHC.Internal.List.cycle        :: {v: [a] | len(v) > 0 } -> [a]
lazy GHC.Internal.List.cycle

assume GHC.Internal.List.takeWhile    :: (a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}
assume GHC.Internal.List.dropWhile    :: (a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}

assume GHC.Internal.List.take :: n:GHC.Types.Int
     -> xs:[a]
     -> {v:[a] | if n >= 0 then (len v = (if (len xs) < n then (len xs) else n)) else (len v = 0)}
assume GHC.Internal.List.drop :: n:GHC.Types.Int
     -> xs:[a]
     -> {v:[a] | (if (n >= 0) then (len(v) = (if (len(xs) < n) then 0 else len(xs) - n)) else ((len v) = (len xs)))}

assume GHC.Internal.List.splitAt :: n:_ -> x:[a] -> ({v:[a] | (if (n >= 0) then (if (len x) < n then (len v) = (len x) else (len v) = n) else ((len v) = 0))},[a])<{\x1 x2 -> (len x2) = (len x) - (len x1)}>
assume GHC.Internal.List.span    :: (a -> GHC.Types.Bool)
        -> xs:[a]
        -> ({v:[a]|((len v)<=(len xs))}, {v:[a]|((len v)<=(len xs))})

assume GHC.Internal.List.break :: (a -> GHC.Types.Bool) -> xs:[a] -> ([a],[a])<{\x y -> (len xs) = (len x) + (len y)}>

assume GHC.Internal.List.reverse      :: xs:[a] -> {v: [a] | len(v) = len(xs)}

//  Copy-pasted from len.hquals
qualif LenSum(v:[a], xs:[b], ys:[c]): len([v]) = (len([xs]) + len([ys]))
qualif LenSum(v:[a], xs:[b], ys:[c]): len([v]) = (len([xs]) - len([ys]))

assume GHC.Internal.List.!!         :: xs:[a] -> {v: _ | ((0 <= v) && (v < len(xs)))} -> a


assume GHC.Internal.List.zip :: xs : [a] -> ys:[b]
            -> {v : [(a, b)] | ((((len v) <= (len xs)) && ((len v) <= (len ys)))
            && (((len xs) = (len ys)) => ((len v) = (len xs))) )}

assume GHC.Internal.List.zipWith :: (a -> b -> c)
        -> xs : [a] -> ys:[b]
        -> {v : [c] | (((len v) <= (len xs)) && ((len v) <= (len ys)))}

assume GHC.Internal.List.errorEmptyList :: {v: _ | false} -> a
@-}
