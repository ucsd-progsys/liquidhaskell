{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module T1371_Tick where

data Foo = Tick Foo | Tock Foo | Fin deriving (Show)

{-@ reflect tx @-}
tx :: Foo -> Foo
tx (Tock x) = Tock (tx x)
tx (Fin)    = Fin
tx (Tick x) = go x

{-@ reflect go @-}
go :: Foo -> Foo
go Fin      = Tick Fin
go (Tick x) = tx x
go (Tock x) = Tock (tx (Tick x))

{-@ thm :: x:Foo -> {x = tx x} @-}
thm :: Foo -> ()
thm Fin    = ()
thm (Tick x) = thm x
thm (Tock x) = thm x
