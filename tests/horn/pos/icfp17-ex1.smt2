(fixpoint "--eliminate=horn")

(var $k (Int))

(constraint
  (forall ((x Int) (x >= 0))
    (and
      (forall ((v Int) (v = x - 1))
       (($k v)))
      (forall ((y Int) ($k y))
        (forall ((v Int) (v = y + 1))
          ((v >= 0)))))))


