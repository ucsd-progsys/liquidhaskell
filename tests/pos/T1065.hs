{-# LANGUAGE TypeFamilies #-}
module T1065 where

-- LH should be able to prove this program terminating
-- See NOTE [Don't choose transform-rec binders as decreasing params]
groupByFB :: ([a] -> lst -> lst) -> lst -> (a -> a -> Bool) -> [a] -> lst
groupByFB c n eq xs0 = groupByFBCore xs0
  where groupByFBCore [] = n
        groupByFBCore (x:xs) = c (x:ys) (groupByFBCore zs)
            where (ys, zs) = span (eq x) xs

