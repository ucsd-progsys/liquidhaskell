

Current Syntax                     Future Syntax

- Abstract Refinements

List <{\x v -> v >= x}> Int        List Int (\x v -> v >= x)
[a<p>]<{\x v -> v >= x}>           [a p] (\x v -> v >= x) (??)
Int<p>                             Int p 
Int<\x -> x >=0>                   Int (\x -> x >= 0) 
Maybe <<p>> (a<q>) (?)             Maybe (a q) p


- Type Arguments

ListN a {len xs + len ys}          ListN a (len xs + len ys)



Q:How do I distinguish `Int p` with `ListN a n`?
(`p` is a abstract refinement and `n` is an `Integer`)
A: From the context! 
Use simple kinds, i.e. 
`ListN :: * -> Int -> *`
`Int :: ?AR -> *`
