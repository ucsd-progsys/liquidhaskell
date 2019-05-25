(fixpoint "--eliminate=horn")

(var $ka ((Int)))
(var $kb ((Int)))
(var $kc ((Int)))

(constraint
 (and
  (forall ((a Int) ($ka a))
   (forall ((v Int) (v = a - 1)) (($kb v))))
  (forall ((b Int) ($kb b))
   (forall ((v Int) (v = b + 1))
    (($kc v))))
  (forall ((v Int) (v >= 0)) (($ka v)))
  (forall ((v Int) ($kc v)) ((v >= 0)))))

