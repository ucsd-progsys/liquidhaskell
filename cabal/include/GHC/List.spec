module spec GHC.List where 

assume replicate        :: n: Int -> a -> {v: [a] | len(v) = n }
assume take             :: n: Int -> [a] -> {v: [a] | len(v) = n }
assume length           :: x: [a] -> { v: Int | v = len(x) }
assume tail             :: xs:[a] -> {v:[a] | len(v) = len(xs) - 1}
assume zipWith          :: f:(p:a -> q:b -> c) 
                           -> xs : [a] 
                           -> ys:{v:[b] | len(v) = len(xs)} 
                           -> {v : [c] | len(v) = len(xs)} 
