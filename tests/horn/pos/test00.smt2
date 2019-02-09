// TODO move to actual SMTLIB format 
(fixpoint "--eliminate=horn")

(qualif  Foo ((v Int) (x Int)) (v = x))
(qualif  Bar ((v Int) (x Int)) (v > x))

(var $k1 (Int Int Int))
(var $k2 (Int Int Int))
(var $k3 (Int Int Int))

(constraint
  (forall ((x Int) (x > 0))
    (forall ((y Int) (y > x))
      (forall ((v Int) (v = x + y)) 
         ((v > 0))))))
