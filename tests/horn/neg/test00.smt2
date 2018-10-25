// TODO move to actual SMTLIB format 

(forall ((x Int) (x > 0))
  (forall ((y Int) (y > x))
    (forall ((v Int) (v = x + y)) 
       (v > 10))))
