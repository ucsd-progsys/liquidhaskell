// we want this to fail because FingerTree is NOT a 'regular' datatype. See `isRegularDataDecl`

(data Node 1 = [
       | Node3 {Node3_lqdc_select_Node3_1 : @(0), Node3_lqdc_select_Node3_2 : @(0), Node3_lqdc_select_Node3_3 : @(0)}
       | Node2 {Node2_lqdc_select_Node2_1 : @(0), Node2_lqdc_select_Node2_2 : @(0)}
])

(data Digit 1 = [
       | Four {Four_lqdc_select_Four_1 : @(0), Four_lqdc_select_Four_2 : @(0), Four_lqdc_select_Four_3 : @(0), Four_lqdc_select_Four_4 : @(0)}
       | Three {Three_lqdc_select_Three_1 : @(0), Three_lqdc_select_Three_2 : @(0), Three_lqdc_select_Three_3 : @(0)}
       | Two {Two_lqdc_select_Two_1 : @(0), Two_lqdc_select_Two_2 : @(0)}
       | One {One_lqdc_select_One_1 : @(0)}
])

(data FingerTree 1 = [
       | Deep {Deep_lqdc_select_Deep_1 : (Digit @(0)), Deep_lqdc_select_Deep_2 : (FingerTree (Node @(0))), Deep_lqdc_select_Deep_3 : (Digit @(0))}
       | Single {Single_lqdc_select_Single_1 : @(0)}
       | EmptyT {}
])


(constant len (func(1, [(FingerTree @(0)), int])))

(define len(l: [a]) : int = {
  if (is$VNil l) then 0 else (1 + len(tail l))
})

(constraint
  (forall ((x (FingerTree int)) (true))
    (forall ((y (FingerTree int)) (y = x)) 
      (forall ((z (FingerTree int)) (z = y)) 
        (((len z) == (len x)))
      )
    )
  )
)
