module spec GHC.List where 

import GHC.Base

head         :: xs:{v: [a] | len v > 0} -> {v:a | v = head xs}
tail         :: xs:{v: [a] | len v > 0} -> {v: [a] | len(v) = (len(xs) - 1) && v = tail xs}

last         :: xs:{v: [a] | len v > 0} -> a
init         :: xs:{v: [a] | len v > 0} -> {v: [a] | len(v) = len(xs) - 1}
null         :: xs:[a] -> {v: GHC.Types.Bool | ((v) <=> len(xs) = 0) }
length       :: xs:[a] -> {v: GHC.Types.Int | v = len(xs)}
filter       :: (a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}
scanl        :: (a -> b -> a) -> a -> xs:[b] -> {v: [a] | len(v) = 1 + len(xs) }
scanl1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) }
foldr1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> a
scanr        :: (a -> b -> b) -> b -> xs:[a] -> {v: [b] | len(v) = 1 + len(xs) }
scanr1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) }

lazy GHC.List.iterate
iterate :: (a -> a) -> a -> [a]

repeat :: a -> [a]
lazy GHC.List.repeat

replicate    :: n:Nat -> x:a -> {v: [{v:a | v = x}] | len(v) = n}

cycle        :: {v: [a] | len(v) > 0 } -> [a]
lazy cycle

takeWhile    :: (a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}
dropWhile    :: (a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)}

take :: n:GHC.Types.Int
     -> xs:[a]
     -> {v:[a] | if n >= 0 then (len v = (if (len xs) < n then (len xs) else n)) else (len v = 0)}
drop :: n:GHC.Types.Int
     -> xs:[a]
     -> {v:[a] | (if (n >= 0) then (len(v) = (if (len(xs) < n) then 0 else len(xs) - n)) else ((len v) = (len xs)))}

splitAt :: n:_ -> x:[a] -> ({v:[a] | (if (n >= 0) then (if (len x) < n then (len v) = (len x) else (len v) = n) else ((len v) = 0))},[a])<{\x1 x2 -> (len x2) = (len x) - (len x1)}>
span    :: (a -> GHC.Types.Bool) 
        -> xs:[a] 
        -> ({v:[a]|((len v)<=(len xs))}, {v:[a]|((len v)<=(len xs))})

break :: (a -> GHC.Types.Bool) -> xs:[a] -> ([a],[a])<{\x y -> (len xs) = (len x) + (len y)}>

reverse      :: xs:[a] -> {v: [a] | len(v) = len(xs)}

//  Copy-pasted from len.hquals
qualif LenSum(v:[a], xs:[b], ys:[c]): len([v]) = (len([xs]) + len([ys]))
qualif LenSum(v:[a], xs:[b], ys:[c]): len([v]) = (len([xs]) - len([ys]))

GHC.List.!!         :: xs:[a] -> {v: _ | ((0 <= v) && (v < len(xs)))} -> a


zip :: xs : [a] -> ys:[b] 
            -> {v : [(a, b)] | ((((len v) <= (len xs)) && ((len v) <= (len ys)))
            && (((len xs) = (len ys)) => ((len v) = (len xs))) )}

zipWith :: (a -> b -> c) 
        -> xs : [a] -> ys:[b] 
        -> {v : [c] | (((len v) <= (len xs)) && ((len v) <= (len ys)))}

errorEmptyList :: {v: _ | false} -> a
