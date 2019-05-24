(constraint 
  (and
      (forall ((x int) (true))
       (forall ((VV int) (VV == 10))
        ((VV >= 0))))
      (forall ((z int) (true))
       (and
        (forall ((r int) (r >= 0))
         (forall ((v int) (v >= 0 && v == r))
          (((v >= 0)))))
        (forall ((_t1 int) (_t1 >= 0))
         (forall ((v int) (v >= 0))
          (((v >= 0)))))))))
