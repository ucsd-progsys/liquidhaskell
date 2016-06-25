module Bob (bar) where

data Foo a = FooCon a
data Dict = DictCon

{-@ foo :: {v:Foo Int | false} @-}
foo = undefined :: Foo Int

{-@ mkDict :: Foo Int -> Dict @-}
mkDict :: Foo Int -> Dict
mkDict _ = DictCon

dict      = mkDict dictList
dictList  = readListPrecDefault dict

{-@ readListPrecDefault :: Dict -> Foo Int @-}
readListPrecDefault :: Dict -> Foo Int
readListPrecDefault = undefined

{-@ bar :: Nat @-}
bar :: Int
bar = 2 - 10
