-- | In general, a module exports all type aliases it defines and those
-- from its trasitive dependencies. This test documents what is stored in the spec in
-- the case of conflicting names, by showing what is imported in such cases.
--
-- We have the following dependency graph:
--
--               NatFoo
--              /   |  \
--             /    |   \
--            /     |    \
--           /      |     \
--          /       |      \
--         /        |       \
--       Nat1      Nat2      \
--         \        /         \
--          \      /           \
--   QualifiedTypeAliases   TypeAliasShadowing
--                \              /
--                 \            /
--                  \          /
--                ImportedTypeAlias
--
-- The sole export of 'NatFoo' is a type alias of the same same.
-- As there is no conflicting name anywhere, no ambiguity arises even though
-- its brought into scope from distinct imports. So the transitive accumulation
-- of aliases is consistent. In this case, both qualified or unqualified ocurrances
-- correspond to the same alias.
--
-- Both @Nat*@ modules define the same type alias @INat@.
-- The implementation is such that in this case, only the definition from the
-- last module (lexicographically) is exported by 'QualifiedTypeAliases'.
-- So here, the only the definition of @INat@ from @Nat2@ refining 'Int32' is
-- in scope (while the @INat@ from @Nat1@, refining 'Int', is not).
--
-- On the other hand, the definition of the type alias @Nat@ implicitly imported
-- by 'Prelude' is shadowed in 'TypeAliasShadowing' by a new definition refining
-- 'Integer' instead of 'Int'. If we try to use 'Nat' unqualified we get
-- and ambiguous name error because the one from 'Prelude' is in scope,
-- so we need to explicitly qualify all uses of @Nat@ here.
module ImportedTypeAlias where

import Data.Int (Int32)
import QualifiedTypeAliases ()
import TypeAliasShadowing ()

{-@ foo :: INat @-}
foo :: Int32
foo = 0

{-@ bar :: Prelude.Nat @-}
bar :: Int
bar = 1

{-@ baz :: TypeAliasShadowing.Nat @-}
baz :: Integer
baz = 2

{-@ testFoo :: NatFoo @-}
testFoo :: Int
testFoo = 3

{-@ testFoo' :: QualifiedTypeAliases.NatFoo @-}
testFoo' :: Int
testFoo' = 4

{-@ testFoo'' :: TypeAliasShadowing.NatFoo @-}
testFoo'' :: Int
testFoo'' = 5
