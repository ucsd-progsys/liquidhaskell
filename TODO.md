# TODO

* tests/pos/NormalForm.hs.fq

```haskell
(\x y -> meraki x) == \x -> ((\z -> (\y -> meraki x)) (meraki x))
```

BETA 1:

  ((\z -> (\y -> meraki x)) (meraki x))

  ==

  (\y -> meraki x)
