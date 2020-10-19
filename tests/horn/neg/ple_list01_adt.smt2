(fixpoint "--rewrite")

(data Vec 1 = [
  | VNil  { }
  | VCons { head : @(0), tail : Vec @(0)}
])

(constant len (func(1, [(Vec @(0)), int])))

(define len(l: [a]) : int = {
  if (is$VNil l) then 0 else (1 + len(tail l))
})

(constraint
  (forall ((x int) (true))
    (forall ((y int) (y = 2)) 
      (forall ((z int) (z = 3)) 
        ((len (VCons x (VCons y (VCons z VNil))) = 30))
      )
    )
  )
)