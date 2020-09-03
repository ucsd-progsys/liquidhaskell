{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
module T1749 where 

data Value = B Bool | I Int

data Op = IF Op Op | NOP

{-@ reflect run @-}
{-@ run ::
       op : Op
  -> { is : [Value] | isValid op (stackType is) }
  -> [Value] @-}
run :: Op -> [Value] -> [Value]
run (IF o1 o2) ((B True):s)  = run o1 s
run (IF o1 o2) ((B False):s) = run o2 s
run NOP s                    = s

data StackType =
    AnyStack
  | IntValueAnd  StackType
  | BoolValueAnd StackType

{-@ reflect stackType @-}
stackType :: [Value] -> StackType
stackType []         = AnyStack
stackType ((I _):xs) = IntValueAnd (stackType xs)
stackType ((B _):xs) = BoolValueAnd (stackType xs)

{-@ reflect isValid @-}
isValid :: Op -> StackType -> Bool
isValid (IF lhs rhs)  (BoolValueAnd s)              = isValid lhs s && isValid rhs s
isValid NOP           _                             = True
isValid _             _                             = False