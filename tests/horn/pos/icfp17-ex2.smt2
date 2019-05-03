(fixpoint "--eliminate=horn")

(var $kx (Int))
(var $ky (Int))

(constraint
  (forall ((x Int) (x >= 0))
    (and
      (forall ((n Int) (n = x - 1))
       (forall ((p Int) (p = x + 1))
         (and
           (forall ((v Int) (v = n)) (($kx v)))
           (forall ((v Int) (v = p)) (($ky v)))
           (forall ((v Int) ($kx p)) (($ky v))))))
      (forall ((y Int) ($ky y))
        (forall ((v Int) (v = y + 1))
          ((v >= 0)))))))


