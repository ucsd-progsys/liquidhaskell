module Interpreter where 

data Exp   a = EConst Int

data Instr a = IConst Int


{-@ measure instrDenote @-}
instrDenote :: Instr a ->  Maybe Int
instrDenote (IConst _) = Nothing

