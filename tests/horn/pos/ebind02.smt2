// TODO: make this the default option
(fixpoint "--eliminate=some")

(var $k (Int))

(constraint
  (forall ((m Int) (true))
    (forall ((z Int) (z = m - 1))
      (and
        (forall ((v1 Int) (v1 = z + 2)) (($k v1)))
        (exists ((x1 Int) (true))
          (and
            (forall ((v2 Int) ($k v2)) ((v2 = x1)))
            (forall ((v3 Int) (v3 = x1 + 1)) ((v3 = m + 2)))))))))
