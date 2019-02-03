(constraint
  (forall ((m Int) (true))
    (exists ((x1 Int) (true))
      (and
        (forall ((v Int) (v = m + 1)) ((v = x1)))
        (forall ((v Int) (v = x1 + 1)) ((v = 2 + m)))))))
