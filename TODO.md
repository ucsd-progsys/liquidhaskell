# TODO


## [NOTE: Boolean Ordering]

SMTLIB doesn't support comparisons

```
x < y
```

on `x, y : Bool`, so we must elaborate the above to:

```
(smt_bool_int x) < (smt_bool_int y)
```

and define in the SMT prelude:

```
  (define-fun smt_bool_int ((b Bool)) Int (ite b 1 0))
  (assert (= (smt_bool_int false) 1))
```

1. define a `smt_bool_int :: Symbol` (same place as `smt_set_add` etc.)
2. define the function `smt_bool_int` in the PRELUDE
3. extend `elaborate` to convert

```haskell
elab (e1 `r` e2) = e1' `r` e2'
  | e1, e2 :: TBool
  where
    [e1', e2']   = smt_bool_int . elab <$> [e1, e2]
```
