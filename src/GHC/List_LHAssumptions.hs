{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.List_LHAssumptions where

import GHC.List
import GHC.Types_LHAssumptions()
import Prelude hiding (foldr1, length, null)

{-@
assume head         :: xs:{v: [a] | len v > 0} -> {v:a | v = head xs}
assume tail         :: xs:{v: [a] | len v > 0} -> {v: [a] | len(v) = (len(xs) - 1) && v = tail xs}

assume last         :: xs:{v: [a] | len v > 0} -> a
assume init         :: xs:{v: [a] | len v > 0} -> {v: [a] | len(v) = len(xs) - 1}
assume null         :: xs:[a] -> {v: Bool | ((v) <=> len(xs) = 0) }
assume length       :: xs:[a] -> {v: Int | v = len(xs)}
assume filter       :: (a -> Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}
assume scanl        :: (a -> b -> a) -> a -> xs:[b] -> {v: [a] | len(v) = 1 + len(xs) }
assume scanl1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) }
assume foldr1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> a
assume scanr        :: (a -> b -> b) -> b -> xs:[a] -> {v: [b] | len(v) = 1 + len(xs) }
assume scanr1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) }

lazy iterate
assume iterate :: (a -> a) -> a -> [a]

assume repeat :: a -> [a]
lazy repeat

assume replicate    :: n:Nat -> x:a -> {v: [{v:a | v = x}] | len(v) = n}

assume cycle        :: {v: [a] | len(v) > 0 } -> [a]
lazy cycle

assume takeWhile    :: (a -> Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}
assume dropWhile    :: (a -> Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}

assume take :: n:Int
     -> xs:[a]
     -> {v:[a] | if n >= 0 then (len v = (if (len xs) < n then (len xs) else n)) else (len v = 0)}
assume drop :: n:Int
     -> xs:[a]
     -> {v:[a] | (if (n >= 0) then (len(v) = (if (len(xs) < n) then 0 else len(xs) - n)) else ((len v) = (len xs)))}

assume splitAt :: n:_ -> x:[a] -> ({v:[a] | (if (n >= 0) then (if (len x) < n then (len v) = (len x) else (len v) = n) else ((len v) = 0))},[a])<{\x1 x2 -> (len x2) = (len x) - (len x1)}>
assume span    :: (a -> Bool)
        -> xs:[a]
        -> ({v:[a]|((len v)<=(len xs))}, {v:[a]|((len v)<=(len xs))})

assume break :: (a -> Bool) -> xs:[a] -> ([a],[a])<{\x y -> (len xs) = (len x) + (len y)}>

assume reverse      :: xs:[a] -> {v: [a] | len(v) = len(xs)}

//  Copy-pasted from len.hquals
qualif LenSum(v:[a], xs:[b], ys:[c]): len([v]) = (len([xs]) + len([ys]))
qualif LenSum(v:[a], xs:[b], ys:[c]): len([v]) = (len([xs]) - len([ys]))

assume !! :: xs:[a] -> {v: _ | ((0 <= v) && (v < len(xs)))} -> a


assume zip :: xs : [a] -> ys:[b]
            -> {v : [(a, b)] | ((((len v) <= (len xs)) && ((len v) <= (len ys)))
            && (((len xs) = (len ys)) => ((len v) = (len xs))) )}

assume zipWith :: (a -> b -> c)
        -> xs : [a] -> ys:[b]
        -> {v : [c] | (((len v) <= (len xs)) && ((len v) <= (len ys)))}

assume errorEmptyList :: {v: _ | false} -> a
@-}
