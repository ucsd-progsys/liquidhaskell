# TODO

## Horn

- [x] test!

Steal SMTLIB parser from here:

- https://github.com/connerirwin/musfix/blob/master/src/Language/SMT/Parser.hs

## Existential Binders

See `tests/pos/ebind-0{0, 1, 2}.fq` which respectively correspond to:

```haskell
exists x1:Int. true => 
/\  forall v1:Int. v1 = 10     => v1 = x1              ... (1)
/\  forall v2:Int. v2 = x1 + 1 => v2 = 11              ... (2)
```

```haskell
forall m:Int. true =>
  exists x1:Int. true =>
  /\  forall v2:Int. v2 = m + 1  => v2 = x1            ... (2)
  /\  forall v3:Int. v3 = x1 + 1 => v3 = m+2           ... (3)
```

```haskell
forall m:Int. true =>
/\ forall z:Int. z = m - 1 =>
   /\ forall v0:Int.  v0 = z + 2  => K(v0)             ... (0)
      /\ exists x1:Int. true =>
         /\  forall v2:Int. K(v2)       => v2 = x1     ... (2)
         /\  forall v3:Int. v3 = x1 + 1 => v3 = m+2    ... (3)
```

