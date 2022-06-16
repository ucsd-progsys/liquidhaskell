{-@ LIQUID "--expect-any-error" @-}
module T743_mini (bar) where

{-@ bar :: Nat @-}
bar :: Int
bar = 2 - 10

data Foo a = FooCon a
data Dict = DictCon


{-@ mkDict :: Foo Int -> Dict @-}
mkDict :: Foo Int -> Dict
mkDict _ = DictCon

dict      = mkDict dictList
dictList  = readListPrecDefault dict

{-@ readListPrecDefault :: Dict -> Foo Int @-}
readListPrecDefault :: Dict -> Foo Int
readListPrecDefault = undefined
