{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple" @-} 

module ReflectLib6 where

data Day = Mon | Tue

{-@ reflect next @-}
next :: Day -> Day
next Mon = Tue
next Tue = Mon

{-@ testFAIL :: { next Mon == Tue } @-}
testFAIL = ()
