(fixpoint "--rewrite")
(fixpoint "--save")
(fixpoint "--fuel=6")

(constant sum  (func(0, [int, int])))

(define sum(n : int) : int = { if (n <= 0) then (0) else (n + sum (n-1)) })

(constraint 
   (forall ((x int) ((5 <= x) && (0 <= (sum (x-5))))) 
       ((15 <= (sum x)))
   )
)

