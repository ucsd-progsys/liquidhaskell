# TODO

$ stack exec -- fixpoint tests/todo/MJBug.hs.bfq --rewrite --noincr +RTS -xc

$ stack exec -- fixpoint tests/todo/MJBug.hs.bfq --rewrite --noincr


Trace: [EVAL-REC-APP[] : Stop : Hw3.nnf (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK)))] 

    if is$Hw3.Var (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK)))) 
        then
            Hw3.Not (Hw3.Var (Hw3.Var##lqdc##$select##Hw3.Var##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK)))))) 
        else
            (if is$Hw3.Not (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK)))) then Hw3.nnf (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK))))) else (if is$Hw3.Or (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK)))) then Hw3.And (Hw3.nnf (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK))))))) (Hw3.nnf (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##2 (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK))))))) else Hw3.Or (Hw3.nnf (Hw3.Not (Hw3.And##lqdc##$select##Hw3.And##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK))))))) (Hw3.nnf (Hw3.Not (Hw3.And##lqdc##$select##Hw3.And##2 (Hw3.Not##lqdc##$select##Hw3.Not##1 (Hw3.Not (Hw3.Or##lqdc##$select##Hw3.Or##1 (Hw3.Not##lqdc##$select##Hw3.Not##1 ds_d3nK)))))))))




    nnf x = if cond then E1 else E2


    nnf e ==> if cond then E1 [x := e ] else E2 [x := e]
              
                E1 [x := e]


