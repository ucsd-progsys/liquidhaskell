# TODO

Current status:

```
rjhala@borscht ~/r/s/liquid-fixpoint (graphs) [1]> stack exec -- fixpoint tests/todo/zipper0.hs.bfq --eliminate
```

yields

```
**** DONE:  Eliminate **********************************************************
Done solving.
fixpoint: 
**** ERROR *********************************************************************
**** ERROR *********************************************************************
**** ERROR *********************************************************************
substSorts has a badExpr
**** ERROR *********************************************************************
**** ERROR *********************************************************************
**** ERROR *********************************************************************

Callstack:
  error, called at src/Language/Fixpoint/Misc.hs:113:14 in liqui_2ENlCpF8HqEB3KcVQQoHPJ:Language.Fixpoint.Misc
  errorstar, called at src/Language/Fixpoint/Solver/Solution.hs:236:11 in liqui_2ENlCpF8HqEB3KcVQQoHPJ:Language.Fixpoint.Solver.Solution
```

