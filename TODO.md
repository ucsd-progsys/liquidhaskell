# TODO

## UNSOUND tests

+ tests/neg/elim00.hs
+ tests/todo/elim00.hs.fq

## hanging tests

+ Data/Text/Fusion.hs


```
$ stack exec -- fixpoint tests/todo/RBTree-ord.hs.fq --eliminate
```

Solution: use the cuts?

1. shift the addKut business to `consBind`
2. check: if RBTree-ord.hs works
3. check: performance hits (with regular solving)
4. use: `deps` inside worklist (not the "suggested" cuts in `F.kuts`)
5. check: performance hits

