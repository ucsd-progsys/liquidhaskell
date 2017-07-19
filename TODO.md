# TODO

## Proper Encoding of DataTypes


https://github.com/ucsd-progsys/liquidhaskell/issues/1048

foo :: Int -> Int -> Int

foo 2 3 ~~~> (int_apply (int_apply foo 2) 3)

apply_T1_clos :: (clos, T1) -> clos
apply_T2_T3   :: (clos, T2) -> T3

bar :: T1 -> T2 -> T3
bar x1 x2 ~~~> apply_T2_T3(apply_T1_clos(bar, x1)), x2)

```
$ fixpoint tests/todo/adt_bin_0.fq > log 2>&1

Trace: [elabExpr] : ((prop : func(0, [Binary;
                  Bin])) (p : Binary) : Bin) == ((mkBin : func(0, [int;
                                                                   Bin])) (n : int) : Bin)
&& ((prop : func(0, [Binary;
                     Bin])) (p : Binary) : Bin) == ((mkBin : func(0, [int;
                                                                      Bin])) (0 : int) : Bin) : bool
```

That is, the `elabExpr` and underneath it, `elabAs` are doing their business.
We just need to 

* hijack wherever the `int_apply` (`intApplyName`) to generalize to non-int,

* traverse the elaborated SInfo and find all the generated `apply_S_T` terms
  to pre-declare to SMT.
