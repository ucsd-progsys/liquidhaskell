{-# LANGUAGE TypeFamilies #-}
module GroupBy where

groupByFB :: ([a] -> lst -> lst) -> lst -> (a -> a -> Bool) -> [a] -> lst
groupByFB c n eq xs0 = groupByFBCore xs0
        {- groupByFBCore :: zoo:_ -> _ / [len zoo] @-}
        {- groupByFBCore :: c:_ -> n:_ -> eq:_ -> xs0:_ -> zoo:_ -> _ / [len zoo] @-}
        {- Decrease groupByFBCore 5 @-}
  where groupByFBCore [] = n
        groupByFBCore (x:xs) = c (x:ys) (groupByFBCore zs)
            where (ys, zs) = span (eq x) xs

