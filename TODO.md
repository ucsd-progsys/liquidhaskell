# TODO

## Qualifier Templates

Change qualfier-parameter to datatype: 

```haskell
data QualParam = QP 
  { qpName    :: !Symbol
  , qpPattern :: !QualPattern 
  } 

data QualPattern 
  = PatNone 
  | PatPrefix !Symbol 
  | PatSuffix !Symbol 
```


* see tests/pos/qualif-template-00.fq
* see tests/pos/qualif-template-01.fq
 
