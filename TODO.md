# TODO

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
