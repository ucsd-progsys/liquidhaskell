# TODO

## Proper Encoding of DataTypes

```
$ stack exec -- fixpoint tests/todo/adt.fq
$ z3 adt.fq

(error "line 16 column 48: invalid function application for cons, sort mismatch on argument at position 2, expected Vec but given Int")
```

HEREHEREHEREHERE

- Don't embed `Vec Int` as just `Int` -- use actual SMTLIB interpretations
for sorts with declared ADT.
- Should be easy to fix by treating `Vec` as an interpreted sort?




### Refactoring

+ [OK] Refactor `theorySymbols` to make them extensible

### Types

+ [OK] `data DataDecl = ...`
+ [OK] GInfo + [DataDecl]

### Parse

+ [OK] dataDeclP :: Parser DataDecl
+ [OK] use the above when parsing FInfo

### Theories

+ [OK] dataDeclSymbols :: DataDecls -> [(Symbol, TheorySymbol)]

### Sanitize

+ [OK] symbolEnv : dataDeclSymbols + theorySymbols

### ToSmt

+ [OK] `instance SMTLIB2 DataDecl`
+ [OK] Do NOT define functions if `tsInterp == Data`


```fq
data Vec 1 = [
  | nil  { }
  | cons { vHead : @(0), vTail : Vec}
]

// (declare-datatypes (A0) ((Vec nil (cons (head A0) (tail Vec)))))

bind 1 x  : int
bind 2 y  : int
bind 3 xs : List int
bind 4 ys : List int
bind 5 l1 : {v: List int | v = cons x xs }
bind 6 l2 : {v: List int | v = cons y ys }
bind 7 l3 : List int

constraint:
  env [1;2;3;4;5;6]
  lhs {v : int | l1 = l2 }
  rhs {v : int | x = y }
  id 1 tag []

constraint:
  env [1;2;3;4;5;6]
  lhs {v : int | l1 = l2 }
  rhs {v : int | xs = ys }
  id 2 tag []

constraint:
  env [1;3;5;7]
  lhs {v : int | l1 = l3  }
  rhs {v : int | cons? l3 }
  id 3 tag []

constraint:
  env [1;3;5;7]
  lhs {v : int | l1 = l3 }
  rhs {v : int | x = head l3 }
  id 4 tag []

constraint:
  env [1;3;5;7]
  lhs {v : int | l1  = l3 }
  rhs {v : int | nil = tail l3 }
  id 5 tag []
```


```smt2
(declare-datatypes (T) ((Vec nil (cons (head T) (tail Vec)))))
(declare-fun x  () Int)
(declare-fun y  () Int)
(declare-fun xs () (Vec Int))
(declare-fun ys () (Vec Int))
(declare-fun l1 () (Vec Int))
(declare-fun l2 () (Vec Int))
(assert (= l1 (cons x xs)))
(assert (= l2 (cons y ys)))
(assert (= l1 l2))
(assert (not (= x y)))
(check-sat)
```

```smt2
(declare-datatypes (T) ((Vec nil (cons (head T) (tail Vec)))))
(declare-fun x  () Int)
(declare-fun xs () (Vec Int))
(declare-fun l1 () (Vec Int))
(declare-fun l2 () (Vec Int))
(assert (= l1 (cons x xs)))
(assert (= l1 l2))
(assert (not (is-cons l2)))
(check-sat)
```

```smt2
(declare-datatypes (T) ((Vec nil (cons (head T) (tail Vec)))))
(declare-fun x  () Int)
(declare-fun xs () (Vec Int))
(declare-fun l1 () (Vec Int))
(declare-fun l2 () (Vec Int))
(assert (= l1 (cons x xs)))
(assert (= l1 l2))
(assert (not (= x (head l2))))
(check-sat)
```

```smt2
(declare-datatypes (T) ((Vec nil (cons (head T) (tail Vec)))))
(declare-fun x  () Int)
(declare-fun l1 () (Vec Int))
(declare-fun l2 () (Vec Int))
(assert (= l1 (cons x nil)))
(assert (= l1 l2))
(assert (not (= nil (tail l2))))
(check-sat)
```

## Proper Encoding of DataTypes

```
(declare-datatypes (T) ((LL lnil (lcons (lhd T) (ltl LL)))))
(declare-fun l1 () (LL Int))
(declare-fun l2 () (LL Int))
(declare-fun l3 () (LL Int))
(declare-fun x  () Int)
(declare-fun zzz () Int)

(assert (not (= l1 (as lnil (LL Int)))))
(assert (not (= l2 (as lnil (LL Int)))))

(assert (= (lhd l1) (lhd l2)))
(assert (not (= l1 l2)))
(assert (= l3 (lcons x l2)))
(assert (> x 100))
(check-sat)

(get-model)


(declare-fun xs () (LL Int))
(declare-fun ys () (LL Int))
(declare-fun y  () Int)

(assert (= xs (as lnil (LL Int))))
(assert (= ys (lcons y ys)))
(assert (= xs ys))
(check-sat)


;; (assert (= (ltl l1) (ltl l2)))
;; (check-sat)
```
