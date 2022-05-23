module FlipArgs where

-------------------------------------------------------------------------------
-- | How to use bounds when the argument orders are backwards -----------------
--   https://github.com/ucsd-progsys/liquidhaskell/issues/1452
-------------------------------------------------------------------------------

import qualified Data.Vector as V 

-------------------------------------------------------------------------------
-- | Warmup example: suppose we require `bar` to have the following type
-------------------------------------------------------------------------------

{-@ bar :: x:Int -> {y:Int | y < x} -> Int @-}
bar :: Int -> Int -> Int 
bar x y = x + y 

-------------------------------------------------------------------------------
-- | `testOK` is SAFE as the signature of `fooOK` says it only calls its 
--    argument with values less than `a` 
-------------------------------------------------------------------------------

{-@ fooOK :: a:Int -> ({v:Int | v <= a} -> Int) -> Int @-} 
fooOK :: Int -> (Int -> Int) -> Int 
fooOK a f = f a + f (a - 1) + f (a - 2)

testOK :: Int
testOK = fooOK 7 (bar 10) 


-------------------------------------------------------------------------------
{- | Naively, `testBAD` is REJECTED as we have no way to say what values the 
     closure will be called with! (Remove the signature to see this)
     However in the below, we say that the closure is called with Int-satisfying `p`
     where the second Int satisfies `q` SUCH THAT

       forall n, xq. (q xq) => (n <= xq) => (p n) 

     that is only values LESS THAN `xq` satisfy `p`.
     This allows LH to deduce at the callsite 
   
       fooBAD (bar 10) 7
       
     that `bar 10` is only called with Int values that are `<= 7` and hence is safe
     w.r.t. the specification for `bar`!
 -}

{-@ fooBAD :: forall <p :: Int -> Bool, q :: Int -> Bool>. 
                { xq :: Int<q> |- {n:Int | n <= xq} <: Int<p> }
                (Int<p> -> Int) -> Int<q> -> Int
  @-}
fooBAD :: (Int -> Int) -> Int -> Int 
fooBAD f a = f a + f (a - 1) + f (a - 2)

testBAD :: Int
testBAD = fooBAD (bar 10) 7 

-------------------------------------------------------------------------------
-- | In the below signature, the "bound" says that the scanner will be called
--   with indices of type `Int<p>` when run on a `q`-refined vector only when:
--   `p` and `q` satisfy a particular relationship, namely:
--    
--      forall v, vec. (q vec) => 0 <= n < vlen v => (p n)
--    
--   That is, any `Int` satisfying `p` is indeed a valid index for a `vec` satisfyin `q`.
-- 
--   As the actual index satisfies `p` and the vector `xs` satisfies `q`, LH 
--   deduces that the indices used at the call-site within `scannedVector` 
--   are valid for `xs`.
-------------------------------------------------------------------------------

{-@ assume V.iscanl' :: forall <p :: Int -> Bool, q :: V.Vector b -> Bool>.
      { vec :: V.Vector b <<q>> |- {n:Int | 0 <= n && n < vlen vec} <: Int<p> }
      (Int<p> -> a -> b -> a)
      -> a 
      -> xs:(V.Vector b <<q>>) 
      -> {ys:V.Vector a | 1 + vlen xs == vlen ys}
  @-}

scannedVector :: (Num a) => V.Vector a -> V.Vector a
scannedVector xs = V.iscanl' (\idx _ _ -> xs V.! idx) 0 xs

main :: IO ()
main = pure ()
