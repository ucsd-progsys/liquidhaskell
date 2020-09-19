(fixpoint "--rewrite")

(constant adder (func(0, [int, int, int])))

(define adder(x : int, y : int) : int = { x + y })

(constraint 
   (forall ((x int) (x == 5)) 
     (forall ((y int) (y == 6)) 
       (( (adder x y) = 11 ))
     )
   )
)
