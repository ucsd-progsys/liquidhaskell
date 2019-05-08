(var $ka (Int))
(var $kb (Int))

(constraint
(and
 (exists ((x1 Int) (true))
  (and
   (forall ((v Int) (v = 1)) ((v = x1)))
   (forall ((v Int) (v = x1 + 1)) (($ka v)))))
 (exists ((x2 Int) (true))
  (and
   (forall ((v Int) ($ka v)) ((v = x2)))
   (forall ((v Int) (v = x2 + 1)) (($kb v)))))
 (forall ((v Int) ($kb v)) ((v = 5)))))
