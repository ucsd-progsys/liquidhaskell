module ResolveB where

{-@ measure getFoo :: Foo -> Int
    getFoo (Foo x) = x
  @-}

data Foo = Foo Int

data Bar = A | B | C
