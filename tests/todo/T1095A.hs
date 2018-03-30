{-@ LIQUID "--reflection" @-}

module Foo where

data Foo 
  = A Foo Foo Foo 
  | B Foo Foo
  | C Foo
  | D Foo
  | E Foo Int 
  | F Int
  | G Int
  | H 
  | I
  | J  
  | K
  | L
  | M
  | N 
  | X
    
{-@  data Foo [size]
      = A {a1 :: Foo, a2 :: Foo, a3 ::  Foo} 
      | B {b1 :: Foo, b2 :: Foo}
      | C {c  :: Foo}
      | D {d  :: Foo}
      | E {e1 :: Foo, e2 :: Int} 
      | F {f  :: Int}
      | G {g  :: Int}
      | H 
      | I
      | J  
      | K
      | L
      | M
      | N 
      | X
@-}
    
{-@ measure size @-}
size :: Foo -> Integer 
{-@ invariant {t:Foo | 0 <= size t} @-}
{-@ size :: Foo -> {v:Integer |  0 <= v }  @-}
size (A x y z) = 1 + size x + size y + size z 
size (B x y)   = 1 + size x + size y 
size (C x)     = 1 + size x 
size (D x)     = 1 + size x 
size (E x _)   = 1 + size x 
size (F _)     = 1 
size (G _)     = 1 
size _         = 0 
    
foo  :: Foo -> Foo
foo (A X _ _) = X 
foo (A _ X _) = X 
foo (A _ _ X) = X 
foo (B X _)   = X 
foo (B _ X)   = X 
foo (C X)     = X 
foo (D X)     = X 
foo (E X _)   = X 
foo X         = X 
foo (A x y z) = A (foo x) (foo y) (foo z)
foo (B x y)   = B (foo x) (foo y)
foo (C x)     = C (foo x)
foo (D x)     = D (foo x)
foo (E x i)   = E (foo x) i 
foo x         = x 
    