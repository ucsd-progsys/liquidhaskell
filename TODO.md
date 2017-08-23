# TODO

## Proper Encoding of DataTypes

Need to get proper casts.

So

    (Cons 1 Emp)

should be elaborated to

    ((Cons : (int, List int) => List int) (1 : int) (Emp : List int))


1. Rig `checkSym` to call `instantiate`
    - currently returns poly-type (e.g. `forall a. List a`)

2. Change all places where `unify`/`apply` happens to
   ALSO apply the substitutions to the casts.
  
