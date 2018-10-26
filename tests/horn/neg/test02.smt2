// TODO move to actual SMTLIB format 

(var $k0 (Int))

(qualif Foo ((v Int)) ((v > 100)))

(constraint 
  (forall ((x Int) (x > 0))
    (and
      (forall ((y Int) (y > x + 100))
        (forall ((v Int) (v = x + y)) 
          (($k0 v))))
      (forall ((z Int) ($k0 z))
        (forall ((v Int) (v = x + z)) 
          ((v > 200)))))))

