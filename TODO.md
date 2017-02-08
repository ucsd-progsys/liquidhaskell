

# TODO


## Minimize Solutions

```haskell
minmizeSol :: Solution -> SolveM Solution
minimizeSol = undefined
 
minimizeConjuncts :: [(Pred, a)] -> [(Pred, a)]
minimizeConjuncts ps = go ps []
  where
    go []     acc = acc
    go (p:ps) acc = do b <- alreadyImplied ps acc q
                       if b then go ps acc
                            else go ps (p:acc)

alreadyImplied ps acc q = checkValid (pAnd [ p | (p, _) <- ps ++ acc] ) q
```


## Beta-Equivalence

* tests/pos/NormalForm.hs.fq

```haskell
(\x y -> meraki x) == \x -> ((\z -> (\y -> meraki x)) (meraki x))
```


BETA 1:

  ((\z -> (\y -> meraki x)) (meraki x))

  ==

  (\y -> meraki x)
