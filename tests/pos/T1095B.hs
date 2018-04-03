{-@ LIQUID "--reflection"        @-}
{-@ LIQUID "--max-case-expand=0" @-}

module T1095B where

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
    
{-@  data Foo [size] @-}
  
{-@ measure size         @-}
{-@ size :: z:Foo -> Nat @-}
size :: Foo -> Int 
size (A x y z) = 1 + size x + size y + size z 
size (B x y)   = 1 + size x + size y 
size (C x)     = 1 + size x 
size (D x)     = 1 + size x 
size (E x _)   = 1 + size x 
size (F _)     = 1 
size (G _)     = 1 
size _         = 0 

-- with case-expand, the below blows up into a giant
-- function spanning literally thousands of lines!
{-@ reflect hasX @-}
hasX :: Foo -> Bool 
hasX (A X _ _) = True 
hasX (A _ X _) = True 
hasX (A _ _ X) = True 
hasX (B X _)   = True 
hasX (B _ X)   = True 
hasX (C X)     = True 
hasX (D X)     = True 
hasX (E X _)   = True 
hasX X         = True 
hasX _         = False 

foo  :: Foo -> Foo
foo x | hasX x = X 
foo (A x y z) = A (foo x) (foo y) (foo z)
foo (B x y)   = B (foo x) (foo y)
foo (C x)     = C (foo x)
foo (D x)     = D (foo x)
foo (E x i)   = E (foo x) i 
foo x         = x 
