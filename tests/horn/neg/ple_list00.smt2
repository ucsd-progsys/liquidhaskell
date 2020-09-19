(fixpoint "--rewrite")

(constant len (func(1, [(Main.List  @(0)), int])))
(constant Cons (func(2, [@(0), (Main.List  @(0)), (Main.List @(0))])))
(constant Nil  (Main.List @(0)))

(match len Nil = 0)
(match len Cons x xs = (1 + len xs))

(constraint
  ((len (Cons 1 (Cons 2 (Cons 3 Nil))) = 4))
)
