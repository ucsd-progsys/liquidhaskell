(qualif Bar ((v int)) (v >= 0))

(var $k_##1 ((int) (int)))

(constraint
  (and
      (forall ((n int) (true))
       (forall ((cond bool) (cond <=> n <= 0))
        (and
         (forall ((lq_tmp$grd##4 bool) (cond))
          (forall ((VV int) (VV == 0))
           (($k_##1 VV n))))
         (forall ((lq_tmp$grd##4 bool) (not cond))
          (forall ((n1 int) (n1 == n - 1))
           (forall ((t1 int) ($k_##1 t1 n1))
            (forall ((v int) (v == n + t1))
             (($k_##1 v n1)))))))))
      (forall ((y int) (true))
       (forall ((r int) ($k_##1 r y))
        (forall ((ok1 bool) (ok1 <=> 0 <= r))
           (forall ((v bool) (and (v <=> 0 <= r) (v == ok1)))
            ((v)))))))) 


