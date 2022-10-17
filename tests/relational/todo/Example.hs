foo, bar :: Bool -> Int
foo a = if a then 0 else 2
bar b = if b then 1 else 3

{-@ relational foo ~ bar :: x1:Bool -> Int ~ x2:Bool -> Int
                         ~~ x1 == x2 => r1 x1 < r2 x2 @-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- Refinemnet types (non-relational):
{-@ reflect isEven @-}
{-@ isEven :: n:Int -> {v:Bool|(v <=> n mod 2 = 0)} / [if n >= 0 then n else -n] @-}
isEven :: Int -> Bool
isEven 0 = True
isEven n = if (isEven (if n < 0 then n + 1 else n - 1)) then False else True

{-
isEven ~ isEven | n mod 2 /= m mod 2 => r1 n /= r2 m

I. True ~ True | 0 mod 2 /= 0 mod 2 => True /= True   (v)

II. True ~ not (isEven (if m < 0 then m + 1 else m - 1)) 
      | 0 mod 2 /= m mod 2 => True /= not (isEven (if m < 0 then m + 1 else m - 1))   (v)

III. not (isEven (if n < 0 then n + 1 else n - 1)) ~ not (isEven (if m < 0 then m + 1 else m - 1)) 
      | n mod 2 /= m mod 2 => 
         not (isEven (if n < 0 then n + 1 else n - 1)) /= not (isEven (if m < 0 then m + 1 else m - 1))   (v)

         a) isEven (if n < 0 then n + 1 else n - 1) ~ isEven (if m < 0 then m + 1 else m - 1) 
               | n' mod 2 /= m' mod 2 => isEven n' /= isEven m'
         b) isEven (if n < 0 then n + 1 else n - 1) ~ isEven (if m < 0 then m + 1 else m - 1) 
               | n' mod 2 /= m' mod 2 => isEven n' /= isEven m'
         c) isEven (if n < 0 then n + 1 else n - 1) ~ isEven (if m < 0 then m + 1 else m - 1) 
               | n' mod 2 /= m' mod 2 => isEven n' /= isEven m'
-}

{-@ relational isEven ~ isEven :: n:Int -> Bool ~ m:Int -> Bool
                               ~~ n mod 2 /= m mod 2 => r1 n /= r2 m @-}
isEven_isEven :: Int -> Int -> ()
isEven_isEven _ _ = ()



{-@ theorem :: n:Int -> m:Int -> {n mod 2 = m mod 2 => isEven n /= isEven m} / [if n >= 0 then n else -n] @-}
theorem :: Int -> Int -> ()
theorem 0 0 = ()
theorem n 0 = if isEven n then () else ()
theorem 0 m = if isEven m then () else ()
theorem n m = theorem n' m'
 where
  n' = if n < 0 then n + 1 else n - 1
  m' = if m < 0 then m + 1 else m - 1

{- isEven :: n:A -> B @-}
{- isEven :: n:A' -> B' ~ n:A' -> B' ~~ n mod 2 = m mod 2 => false @-}

{- emp |- A <: A'
   A  |- B' <: B -}

-- abs :: Int -> {x:Int|0 <= x}
-- abs x = if x < 0 then -x else x

-- safeDiv :: Int -> {d:Int|d /= 0} -> Int
-- safeDiv = div

-- isEven :: n:Int -> {v:Bool|v <=> n mod 2 = 0}
-- isEven 0 = True
-- isEven n = not $ isEven (if n < 0 then n + 1 else n - 1)

