// TODO move to actual SMTLIB format 

(constraint 
(forall ((x Int) (x > 0))
  (and
    (forall ((y Int) (y > x))
      (forall ((v Int) (v = x + y)) 
        ( (v > 0)  )))
    (forall ((z Int) (z > 10))
      (forall ((v Int) (v = x + z)) 
        ( (v > 100)  )))))
)


