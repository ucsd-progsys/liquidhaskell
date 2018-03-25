## New Syntax for Abstract Refinements

### Ghost Parameters


```haskell
A n -> B (n + 1)

-- becomes
{ p n => q (n + 1)}. A<p> -> B<q>

-- i.e.
{ p n => v = n + 1 => q v}. A<p> -> B<q>
```

which means, I suppose that

```haskell
A n -> B (op n)

-- becomes
{ p n => q (op n) }. A<p> -> B<q>

-- i.e.

{ p n => v = op n => q v }. A<p> -> B<q>
```


(a -> Count b <<p>>) -> xs:List a -> (Count (List b) <<q>>)


```haskell
A n -> B m -> C (n + m)

-- becomes
{ p n => q m => r (n + m) }. A<p> -> B<q> -> C<r>

-- i.e.
{ p n => q m => v = n + m => r v }. A<p> -> B<q> -> C<r>
```

{ n::Int<p> |- {v:Int | v = n+1} <: Int<q> }

```haskell
{-@ bump1 :: forall <p::Int -> Bool, q::Int -> Bool>.
               { n::Int<p> |- {v:Int | v = n + 1} <: Int<q> }
               (Int -> Int<p>) -> Int<q>
  @-}
bump1 :: (Int -> Int) -> Int
bump1 f = f 0 + 1

{-@ bumps :: forall <p::[Int] -> Bool, q::Int -> Bool>.
               { xs :: [Int]<p> |- {v:Int | v = len xs} <: Int<q> }
               (Int -> [Int]<p>) -> Int<q>
  @-}

bumps :: (Int -> ListN Int n) -> IntN n
bumps f = size (f 0)

{-@ bump2 :: forall <p::Int -> Bool, q::Int -> Bool, r::Int -> Bool>.
               { n::Int<p>, m::Int<q> |- {v:Int | v = n + m} <: Int<r> }
               (Int -> Int<p>) -> (Int -> Int<q>) -> Int<r>
  @-}
bump2 :: (Int -> Int) -> (Int -> Int) -> Int
bump2 f g = f 0 + g 0

{-@ flerb :: ({v:Int | v = 6}, {v:Int | v = 10}) @-}
flerb = (a, b)   
  where
    a = bump  zong
    b = bump2 zong zong
    zong :: Int -> Int
    zong n = 5

{-@ type IntN N = {v:Int | v == N} @-}
bump1 :: Ghost n. (Int -> IntN n) -> IntN (n+1)
bump2 :: Ghost n m. (Int -> IntN n) -> (Int -> IntN m) -> IntN (n+m)
```

### New Proposal

**NOTE:** I believe this is a **purely syntactic change**:
it should not affect how absref is actually implemented,
but it more precisely describes the implementation than
the current `-> Bool` formulation.

#### Step 1: Abstract Refinement is "Type with Shape"

Key idea is to think of an abstract refinement as a (function returning a) refinement type.

That is, the abstract refinement:

```haskell
  T1 -> T2 -> T3 -> ... -> S -> Bool
```

now just becomes

```haskell
  T1 -> T2 -> T3 -> ... -> {S}
```

Here, `{S}` denotes a refinement type with shape `S`

**Key Payoff:** This means that we don't need an _explicit application_ form, that is

```haskell
  foo :: forall <p :: Int -> Bool>. [Int<p>] -> Int<p>
```

can just be written as

```haskell
  foo :: forall <p :: {Int}>. [p] -> p
```

where we need not write `Int<p>`, its enough to just write `p`.

#### Step 2: An explicit "Meet" Operator

However, sometimes you need to write things like:

```haskell
  List <p> a <<p>>
```

where `p :: List a -> Bool` i.e. `p :: {List a}` and which denotes

* a list-of-a that is recursively indexed by `p`, AND
* where the top-level list is constrained by `p`.

That is, more generally, where you want to

* additionally, index the type with other abstract refinements, AND
* "apply" an abstract refinement to the "top-level" type.

For this, I think we should have an explicit *meet* operator
Note that, earlier `Int<p>` was an *implicit* meet operator,
where we were *conjoining* `Int` and `p`. Viewing `p` as
just being a refined `Int` allows us to SEPARATE "meet"
to only those places where its really needed.

So we can write the funny `List <p> a <<p>>` as:

```haskell
  p /\ List <p> a
```

See below for many other examples:

#### Example: Value Dependencies

**Old**

```haskell
  foo :: forall <p :: Int -> Int -> Bool>. x:Int -> [Int<p x>] -> Int<p x>
```

**New**

```haskell
  foo :: forall <p :: Int -> {Int}>. x:Int -> [p x] -> p x
```

#### Example: Dependent Pairs

**Old**

```haskell
  data Pair a b <p :: a -> b -> Bool>
    = Pair { pairX :: a
           , pairB :: b<p pairX>
           }

  type OrdPair a = Pair <{\px py -> px < py}> a a
```

**New**

```haskell
  data Pair a b <p :: a -> {b}>
    = Pair { pairX :: a
           , pairY :: p pairX
           }


  type OrdPair a = Pair a a <\px ->  {py:a | px < py}>
```

#### Example: Binary Search Maps

**Old**

```haskell
  data Map k a <l :: root:k -> k -> Bool, r :: root:k -> k -> Bool>
      = Tip
      | Bin { mSz    :: Size
            , mKey   :: k
            , mValue :: a
            , mLeft  :: Map <l, r> (k <l mKey>) a
            , mRight :: Map <l, r> (k <r mKey>) a }

  type OMap k a = Map <{\root v -> v < root }, {\root v -> v > root}> k a
```

**New**

```haskell
  data Map k a <l :: root:k -> {k}, r :: root:k -> {k}>
      = Tip
      | Bin { mSz    :: Size
            , mKey   :: k
            , mValue :: a
            , mLeft  :: Map (l mKey) a <l, r>
            , mRight :: Map (r mKey) a <l, r> }

  type OMap k a = Map k a <\root -> {v:k | v < root }, \root -> {v:k | root < v}>
```

#### Example: Ordered Lists

**Old**

```haskell
  data List a <p :: a -> a -> Bool>
    = Emp
    | Cons { lHd :: a
           , lTl :: List <p> (a<p lHd>)
           }

  type OList a = List <{\x v -> x <= v}> a
```

**New**

```haskell
  data List a <p :: a -> {a}>
    = Emp
    | Cons { lHd :: a
           , lTl :: List (p lHd) <p>
           }

  type OList a = List a <\x -> {v:a | x <= v}>
```

#### Example: Infinite Streams

**Old**

```haskell
  data List a <p :: List a -> Prop>
    = N
    | C { x  :: a
        , xs :: List <p> a <<p>>
        }

  type Stream a = {xs: List <{\v -> isCons v}> a | isCons xs}
```

**New**

```haskell
  data List a <p :: {List a}>
    = N
    | C { x  :: a
        , xs :: p /\ List a <p>
        }

  type Stream a = {xs: List a <{v | isCons v}> | isCons xs}
```




### Old Proposal


|                      | Current Syntax                | Future Syntax                 |
|----------------------|-------------------------------|-------------------------------|
| Abstract Refinements | `List <{\x v -> v >= x}> Int` | `List Int (\x v -> v >= x)`   |
|                      | `[a<p>]<{\x v -> v >= x}>`    | `[a p] (\x v -> v >= x) (??)` |
|                      | `Int<p>`                      | `Int p`                       |
|                      | `Int<\x -> x >=0>`            | `Int (\x -> x >= 0)`          |

|                      | `Maybe <<p>> (a<q>) (?)`      | `Maybe (a q) p`               |
|                      | `Map <l, r> <<p>> k v  (?)`   | `Maybe k v l r p`             |

| Type Arguments       | `ListN a {len xs + len ys}`   | `ListN a (len xs + len ys)`   |

Q: How do I distinguish `Int p` with `ListN a n`?
(`p` is a abstract refinement and `n` is an `Integer`)

A: From the context!
Use simple kinds, i.e.
`ListN :: * -> Int -> *`
`Int :: ?AR -> *`
