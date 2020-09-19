(fixpoint "--rewrite")

(define ints2 (): [int] = { 
   Cons 1 (Cons 20 Nil)
})

(define filter (lq1 : func(0 , [a##a29r;bool]),  lq2 : [a##a29r]) : [a##a29r] = {
  if (isNil lq2) then Nil else (
      if (lq1 (head lq2)) 
        then (Cons (head lq2) (filter lq1 (tail lq2))) 
        else (filter lq1 (tail lq2)))
})

(define ints0 () : [int] = { 
    Cons 0 (Cons 1 (Cons 2 Nil))
})

(define isPos (lq1 : int) : bool = {
    lq1 > 0
})


(match isCons Cons x xs = (true))
(match isNil  Cons x xs = (false))
(match isCons Nil       = (false))
(match isNil  Nil       = (true))
(match tail Cons x xs   = (xs))
(match head Cons x xs   = (x))

(constant isCons (func(1 , [[@(0)], bool])))
(constant isNil  (func(1 , [[@(0)], bool])))
(constant Nil    (func(1 , [[@(0)]])))
(constant tail   (func(1 , [[@(0)], [@(0)]])))
(constant head   (func(1 , [[@(0)], @(0)])))
(constant ints0   [int])
(constant ints2   [int])
(constant filter  (func(1 , [func(0 , [@(0), bool]), [@(0)], [@(0)]])))
                
(constant isPos  (func(0 , [int, bool])))
(constant Cons   (func(1 , [@(0), [@(0)], [@(0)]])))
(constant Nil    (func(1 , [[@(0)]])))

(constraint
  ((filter isPos ints0 == ints2))
)