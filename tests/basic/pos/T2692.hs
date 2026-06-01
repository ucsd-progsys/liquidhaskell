-- | Test that higher-kinded type parameters with self-nesting
-- do not cause a splitC panic due to RProp body depth asymmetry.
-- See GitHub issue #2692.
module T2692 where

data T f a = Cons a (f a)

removeEach :: T [] a -> T [] (a, [a])
removeEach = undefined

test :: T [] (T [] Int) -> T [] (T [] Int, [T [] Int])
test = removeEach
