- Niki Vazou

|                      | Current Syntax                | Future Syntax                 |
|----------------------|-------------------------------|-------------------------------|
| Abstract Refinements | `List <{\x v -> v >= x}> Int` | `List Int (\x v -> v >= x)`   |
|                      | `[a<p>]<{\x v -> v >= x}>`    | `[a p] (\x v -> v >= x) (??)` |
|                      | `Int<p>`                      | `Int p`                       |
|                      | `Int<\x -> x >=0>`            | `Int (\x -> x >= 0)`          |
|                      | `Maybe <<p>> (a<q>) (?)`      | `Maybe (a q) p`               |
|                      | `Map <l, r> <<p>> k v  (?)`   | `Maybe k v l r p`             |
| Type Arguments       | `ListN a {len xs + len ys}`   | `ListN a (len xs + len ys)`   |

Q: How do I distinguish `Int p` with `ListN a n`?
(`p` is a abstract refinement and `n` is an `Integer`)

A: From the context!
Use simple kinds, i.e.
`ListN :: * -> Int -> *`
`Int :: ?AR -> *`

----------------------------

- Chris Tetreault

Currently for specifications, we write them as such:

`{-@ unsafeLookup :: n:Nat ->  {v:Vector a | n < (vlen v)} -> a @-}`

... where we bind `n` as a `Nat` and `v` as a `Vector a` _such that_ `[stuff]`. As a Haskeller, I find it strange to put logic into something that appears to be a function signature. I propose:

```
{-@
   unsafeLookup :: Nat -> Vector a -> a
   unsafeLookup n v _ | n < vlen v
@-}
```

Here we have a "function" that takes a refined type `Nat` and a Haskell type `Vector a` and returns a Haskell type `a`. The definition of this refinement binds the `Nat` to `n` and the `Vector a` to `v`, and doesn't care about the `a`. Next, it specifies that `n < vlen v`.

We could mix the syntax up a bit more to address my previous concern that it not look "too much like haskell", presuably drawing from the list of symbols that get used elsewhere, but I'm more concerned with getting this sort of "function syntax" than with what specific glyphs get used.
