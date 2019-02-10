# TODO

- T1371.hs.bfq

Stack trace:

  Language.Fixpoint.Solver.Instantiate.evalAppAc,
  called from Language.Fixpoint.Solver.Instantiate.evalApp,
  called from Language.Fixpoint.Solver.Instantiate.eval,
  called from Language.Fixpoint.Solver.Instantiate.evalOne,
  called from Language.Fixpoint.Smt.Interface.smtBracket,
  called from Language.Fixpoint.Solver.Instantiate.evaluate,


Trace: [evalApp: ] : is$N : [N (val lq_anf$##7205759403792797318##dXY)]

Trace: [evalAppAc:ePop ] : true

Trace: [PLE: Rewrite -is$Nis$N (N (val lq_anf$##7205759403792797318##dXY)) : true] : 0



 [opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR (opR e2##aVJ)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))]

define killer (e1 : Thing,  e2 : Thing)
  = (((killer e1 e2) = (if (is$N e1
                          then
  							   (if (is$N e2)
								  then e1
								  else (Op (left e2) (killer (N (val e1)) (right e2))))
					      else (Op (left e1) (killer (right e1) e2)))))

define killer (arg1 : Thing,  arg2 : Thing) : Thing = 
  (((killer arg1 arg2) = (if (is$N arg1) then 
                            (if (is$N arg2) then 
                               arg1 
                             else 
                               (Op (opLeft arg2) (bar (N (eNum arg1)) (opRight arg2)))) 
                         else 
                             (Op (opLeft arg1) (bar (opRight arg1) arg2)))))

define Bug.bar (ds_dXI : Bug.Thing,  ds_dXJ : Bug.Thing) = (&& [((Bug.bar ds_dXI ds_dXJ) = (if (is$Bug.N ds_dXI) then (if (is$Bug.N ds_dXJ) then ds_dXI else (Bug.Op (Bug.Op##lqdc##$select##Bug.Op##1 ds_dXJ) (Bug.bar (Bug.N (Bug.N##lqdc##$select##Bug.N##1 ds_dXI)) (Bug.Op##lqdc##$select##Bug.Op##2 ds_dXJ)))) else (Bug.Op (Bug.Op##lqdc##$select##Bug.Op##1 ds_dXI) (Bug.bar (Bug.Op##lqdc##$select##Bug.Op##2 ds_dXI) ds_dXJ))));
                                                                (true => && [((1 + 2) = 3)])])

// KILLS
define killer (arg1 : Thing,  arg2 : Thing) : Thing = 
   (((killer arg1 arg2) = (if (is$N arg1) 
                            then (Op (opLeft arg2) (killer (N (eNum arg1)) (opRight arg2))) 
                            else (Op (opLeft arg1) (killer (opRight arg1) arg2)))))

