# TODO

1. Need to update all transitive deps via ELIMINATED KVars

2. Why are ranks crap ?

3. kvWriteBy, kvReadBy are invalid when we have
   ELIMINATED (non-cut) kvars ...

(a) push eliminate inside Solver.solve

(b) unify construction of graph for eliminate & regular worklist

  
--eliminate (WRONG)

1 := Rank {rScc = 5, rIcc = 5, rTag = [4]}

2 := Rank {rScc = 3, rIcc = 3, rTag = [4]}

4 := Rank {rScc = 4, rIcc = 4, rTag = [3]}

5 := Rank {rScc = 0, rIcc = 0, rTag = [3]}

6 := Rank {rScc = 2, rIcc = 2, rTag = [3]}

10 := Rank {rScc = 1, rIcc = 1, rTag = [1]}


**without** eliminate (CORRECT)

1 := Rank {rScc = 6, rIcc = 6, rTag = [4]}

2 := Rank {rScc = 0, rIcc = 0, rTag = [4]}

3 := Rank {rScc = 1, rIcc = 1, rTag = [3]}

4 := Rank {rScc = 5, rIcc = 5, rTag = [3]}

5 := Rank {rScc = 2, rIcc = 2, rTag = [3]}

6 := Rank {rScc = 4, rIcc = 4, rTag = [3]}

10 := Rank {rScc = 3, rIcc = 3, rTag = [1]}




## UNSOUND tests

Why does REMOVING the extra cut var (see comment in file) cause the other var to
be solved to FALSE? Print out the LHS used for the OTHER var to see why...

+ liquid-fixpoint/tests/todo/elim000.min.fq



+ tests/neg/elim00.hs



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
