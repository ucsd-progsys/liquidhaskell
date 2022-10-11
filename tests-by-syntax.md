# Tests By Syntax

This file lists up-to-date examples of Liquid Haskell syntax. It's guaranteed to be up-to-date since the examples are all test cases!

You may find this list useful if the main documentation becomes out of date with the latest version of Liquid Haskell.

It does *not* intend to explain the features that the syntax implements.

## Basics

### Refining Type Expressions

[Float.hs](tests/basic/pos/Float.hs)
[inc02.hs](tests/basic/pos/inc02.hs)
[Compose.hs](tests/spec/pos/Compose.hs)

### Refining Data Delcarations

[Data01.hs](tests/datacon/pos/Data01.hs)
[NewType.hs](tests/datacon/pos/NewType.hs)
[Date.hs](tests/datacon/pos/Date.hs)

### Creating Liquid Type Synonyms

[Inc03Lib.hs](tests/basic/pos/Inc03Lib.hs)
[alias03.hs](tests/basic/pos/alias03.hs)

## Measures

### Built-In Measures

[Len01.hs](tests/measure/pos/Len01.hs)

### Measures Backed by Custom Haskell Functions

[fst00.hs](tests/measure/pos/fst00.hs)
[GList00Lib.hs](tests/measure/pos/GList00Lib.hs)

### Measures Not Backed By Haskell Functions

[AbsMeasure.hs](tests/measure/pos/AbsMeasure.hs)

## Checking Termination

### Automatic

[Ackermann.hs](tests/terminate/pos/Ackermann.hs)
[AutoTerm.hs](tests/terminate/pos/AutoTerm.hs)
[StructSecondArg.hs](tests/terminate/pos/StructSecondArg.hs)

### Manual

[list00-local.hs](tests/terminate/pos/list00-local.hs)
[list03.hs](tests/terminate/pos/list03.hs)
[LocalTermExpr.hs](tests/terminate/pos/LocalTermExpr.hs)
[Papp00.hs](tests/absref/pos/Papp00.hs)

### Annotating Datatypes

[AutoTerm.hs](tests/terminate/pos/AutoTerm.hs)
[list03.hs](tests/terminate/pos/list03.hs)

## Abstract Refinements

### Binding in Data Declaration

[Map.hs](tests/pos/Map.hs)
[deptup0.hs](tests/absref/pos/deptup0.hs)
[deptupW.hs](tests/absref/pos/deptupW.hs)
[state00.hs](tests/absref/pos/state00.hs)

### Binding via `forall`

[Papp00.hs](tests/absref/pos/Papp00.hs)
[deptupW.hs](tests/absref/pos/deptupW.hs)
[state00.hs](tests/absref/pos/state00.hs)

### Binding via lambdas

[Map.hs](tests/pos/Map.hs)
[ListISort.hs](tests/absref/pos/ListISort.hs)
[ListQSort.hs](tests/absref/pos/ListQSort.hs)
[deppair2.hs](tests/absref/pos/deppair2.hs)

### Application

[Map.hs](tests/pos/Map.hs)
[ListISort.hs](tests/absref/pos/ListISort.hs)
[ListQSort.hs](tests/absref/pos/ListQSort.hs)
[deptup0.hs](tests/absref/pos/deptup0.hs)
[deppair2.hs](tests/absref/pos/deppair2.hs)
[state00.hs](tests/absref/pos/state00.hs)
[VectorLoop.hs](tests/absref/pos/VectorLoop.hs)

### Multi-Parameter Abstract Refinements

[Map.hs](tests/pos/Map.hs)
[VectorLoop.hs](tests/absref/pos/VectorLoop.hs)
[deppair2.hs](tests/absref/pos/deppair2.hs)


## Proofs

### Fully Automated

[ple0.hs](tests/ple/pos/ple0.hs)

### More Manual

[Compiler.hs](tests/ple/pos/Compiler.hs)
[NegNormalForm.hs](tests/ple/pos/NegNormalForm.hs)

### Use Curly Braces

[ple0.hs](tests/ple/pos/ple0.hs)
[Compiler.hs](tests/ple/pos/Compiler.hs)
[NegNormalForm.hs](tests/ple/pos/NegNormalForm.hs)

## Misc.

### Defining Predicates (DEPRECATED in favor of measures)

[alias04.hs](tests/basic/pos/alias04.hs)

### Inlining Functions (DEPRECATED in favor of measures)

[alias05.hs](tests/basic/pos/alias05.hs)
[Date.hs](tests/datacon/pos/Date.hs)
[DoubleLit.hs](tests/reflect/pos/DoubleLit.hs)

### Reflecting Functions

[Ple1Lib.hs](tests/measure/pos/Ple1Lib.hs)
[ple00.hs](tests/measure/pos/ple00.hs)
[ReflString1.hs](tests/reflect/pos/ReflString1.hs)

### `using ... as ...`

[Using00.hs](tests/measure/pos/Using00.hs)

### `autosize` Keyword

[tests/pos/AutoSize.hs](tests/pos/AutoSize.hs)

## `LIQUID` pragmas

TODO (for now, use GitHub search)



