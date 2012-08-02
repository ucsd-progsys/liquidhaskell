module spec GHC.List where 

measure len :: forall a. [a] -> Int
len ([])     = 0
len (y:ys)   = 1 + len(ys)

invariant {v: [a] | len(v) >= 0 }

-- assume replicate        :: n: Int -> a -> {v: [a] | len(v) = n }
-- assume take             :: n: Int -> [a] -> {v: [a] | len(v) = n }
-- assume length           :: x: [a] -> { v: Int | v = len(x) }
-- assume tail             :: xs:[a] -> {v:[a] | len(v) = len(xs) - 1}
-- assume zipWith          :: f:(p:a -> q:b -> c) 
--                           -> xs : [a] 
--                           -> ys:{v:[b] | len(v) = len(xs)} 
--                           -> {v : [c] | len(v) = len(xs)} 
