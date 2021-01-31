# TODO

## PLE Fuel

- [x] add test (e.g. sum needed to unfold 4 times)
- [ ] trace to print out cid/unfold
- [ ] add counter
- [ ] add predicate to filter candidate
- [ ] config option


1. Add a type

```haskell
type FuelCounter = Map Symbol Int
```

2. Add a field `evFuel :: EvalEnv`

3. In `evalApp` update `evFuel`

4. In `evalApp` use `evFuel` to stop unfolding


- `evalStep e` seems to be the key bit where something is extended?
  -> lets trace the `path` ? 
  -> can we bound the `path` ?
