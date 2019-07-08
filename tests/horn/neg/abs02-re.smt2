(fixpoint "--eliminate=horn")

(var $k_##1 ((Int) (Int)))
(var $k_##3 ((Int) (Int)))

(constraint
  (and
      (forall ((x int) (true))
       (forall ((pos bool) (pos <=> x >= 0))
        (and
         (forall ((lq_tmp$grd##3 bool) (pos))
          (forall ((VV int) (VV == x))
           (($k_##1 VV x))))
         (forall ((lq_tmp$grd##3 bool) (not pos))
          (forall ((v int) (v == 0 - x))
           (($k_##1 v x)))))))
      (forall ((z int) (true))
       (and
        (forall ((r int) (r >= 0))
         (forall ((v int) (v == r + 1))
          (($k_##3 v z))))
        (and
         (forall ((_t1 int) (_t1 >= 0))
          (forall ((VV##0 int) ($k_##1 VV##0 _t1))
           (((VV##0 >= 0)))))
         (forall ((res int) ($k_##3 res z))
          (forall ((ok bool) (ok <=> 6660 <= res))
           (forall ((v bool) ((v <=> 6660 <= res) && v == ok))
            ((v))))))))))
