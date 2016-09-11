{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}


{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}

module Main where

import System.Environment   

import Language.Haskell.Liquid.String
import GHC.TypeLits
import Data.String hiding (fromString)
import Prelude hiding ( mempty, mappend, id, mconcat, map
                      , take, drop  
                      , error, undefined 
                      )
import Language.Haskell.Liquid.ProofCombinators 

import Data.Maybe 

import Data.Proxy 
{-@ symbolVal :: forall n proxy. KnownSymbol n => x:proxy n 
  -> {v:String | v == n && v == symbolVal x } @-}
{-@ measure symbolVal :: p n -> String @-}

-------------------------------------------------------------------------------
------------ | Interface ------------------------------------------------------
-------------------------------------------------------------------------------

main :: IO ()
main = 
  do args      <- getArgs
     case args of 
       (i:fname:target:_) -> do input <- fromString <$> readFile fname 
                                runMatching (read i :: Int) input target
       _                -> putStrLn $ "Wrong input: You need to provide the chunksize," ++
                                      "the input filename and the target string. For example:\n\n\n" ++ 
                                      "./StringIndexing 10 input.txt abcab\n\n"
     

runMatching :: Int -> SMTString -> String -> IO ()
runMatching chunksize input tg =
  case someSymbolVal tg of 
    SomeSymbol (_ :: Proxy target) -> do            
      let mi1    = toMI input :: MI target 
      let is1    = indicesMI mi1 
      putStrLn   $ "Serial   Indices: " ++ show is1
      let mi2    = toMIPar chunksize input :: MI target 
      let is2    = indicesMI mi2 
      putStrLn   $ "Parallel Indices: " ++ show is2
      putStrLn   $ "Are equal? " ++ show (is1 == is2)

test = indicesMI (toMI (fromString $ clone 100 "ababcabcab")  :: MI "abcab" )
  where
    clone i xs = concat (replicate i xs) 

toMI   :: forall (target :: Symbol). (KnownSymbol target) => SMTString -> MI target 
toMI input  
  | isNullString input = mempty
  | otherwise          = MI input (makeIndices input (fromString (symbolVal (Proxy :: Proxy target))) 0 (stringLen input - 1))

toMIPar :: forall (target :: Symbol). (KnownSymbol target) => Int -> SMTString -> MI target  
toMIPar chunksize input 
  = pmconcat chunksize (map toMI (chunkString chunksize input))

-------------------------------------------------------------------------------
----------  Indexing Structure Definition -------------------------------------
-------------------------------------------------------------------------------

data MI (target :: Symbol) where 
  MI :: SMTString       -- | input string
     -> (List Int)      -- | valid indices of target in input
     -> MI target
  deriving (Show)

{-@ data MI target 
  = MI { input   :: SMTString
       , indices :: List (GoodIndex input target)
       } @-}

{-@ type GoodIndex Input Target 
  = {i:Int | IsGoodIndex Input Target i }
  @-}

{-@ type GoodIndexTwo Input X Target 
  = {i:Int | (IsGoodIndex Input Target i)  && (IsGoodIndex (concatString Input X) Target i) }
  @-}


{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target <= stringLen Input)
  && (0 <= I)
  @-}

{-@ measure indicesMI @-}
indicesMI (MI _ is) = is 

{-@ measure inputMI @-}
inputMI (MI i _) = i 

-------------------------------------------------------------------------------
----------  Monoid Operators on MI --------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). (KnownSymbol target) =>  MI target
mempty = MI stringEmp N

{-@ reflect mconcat @-}
mconcat :: forall (target :: Symbol). (KnownSymbol target) => List (MI target) -> MI target 
mconcat N        = mempty
mconcat (C x xs) = mappend x (mconcat xs)

{-@ reflect pmconcat @-}
pmconcat :: forall (target :: Symbol). (KnownSymbol target) => Int -> List (MI target) -> MI target 
{-@ pmconcat :: forall (target :: Symbol). (KnownSymbol target) => 
  Int -> is:List (MI target) -> MI target /[llen is] @-}

pmconcat i xs
  | i <= 1 
  = mconcat xs 
pmconcat i N   
  = mempty
pmconcat i (C x N) 
  = x
pmconcat i xs 
  = pmconcat i (map mconcat (chunk i xs))



{-@ reflect mappend @-}
mappend :: forall (target :: Symbol).  (KnownSymbol target) => MI target -> MI target -> MI target
mappend (MI i1 is1) (MI i2 is2)
  = MI (concatString i1 i2)
       ((castGoodIndexRightList (fromString (symbolVal (Proxy :: Proxy target))) i1 i2 is1
          `append`
        makeNewIndices i1 i2 (fromString (symbolVal (Proxy :: Proxy target)))
       ) `append`
       (map (shiftStringRight (fromString (symbolVal (Proxy :: Proxy target))) i1 i2) is2)) 

-- | Helpers 
{-@ reflect shiftStringRight @-}
shiftStringRight :: SMTString -> SMTString -> SMTString -> Int -> Int 
{-@ shiftStringRight :: target:SMTString -> left:SMTString -> right:SMTString -> i:GoodIndex right target 
  -> {v:(GoodIndex {concatString left right} target) | v == i + stringLen left } @-}
shiftStringRight target left right i 
  = cast (subStringConcatFront right left (stringLen target) i) (shift (stringLen left) i)

{-@ reflect makeNewIndices @-}
{-@ makeNewIndices :: s1:SMTString -> s2:SMTString -> target:SMTString -> List (GoodIndex {concatString s1 s2} target) @-}
makeNewIndices :: SMTString -> SMTString -> SMTString -> List Int 
makeNewIndices s1 s2 target
  | stringLen target < 2 
  = N
  | otherwise
  = makeIndices (concatString s1 s2) target
                (maxInt (stringLen s1 - (stringLen target-1)) 0)
                (stringLen s1 - 1)

{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect shift @-}
shift :: Int -> Int -> Int 
shift x y = x + y 

-- | Casting good indices: the below operators are liquid casts and behave like id at runtime

-- NV: The recursion is required as there is no other way to (access &) cast _each_ element of the input list
{-@ reflect castGoodIndexRightList @-}
castGoodIndexRightList :: SMTString -> SMTString -> SMTString -> List Int -> List Int    
{-@ castGoodIndexRightList :: target:SMTString -> input:SMTString -> x:SMTString -> is:List (GoodIndex input target) 
    -> {v:List (GoodIndexTwo input x target) | v == is} @-}
castGoodIndexRightList target input x N 
  = N 
castGoodIndexRightList target input x (C i is) 
  = C (castGoodIndexRight target input x i) (castGoodIndexRightList target input x is)  


{-@ reflect castGoodIndexRight @-}
castGoodIndexRight :: SMTString -> SMTString -> SMTString -> Int -> Int  
{-@ castGoodIndexRight :: target:SMTString -> input:SMTString -> x:SMTString -> i:GoodIndex input target 
   -> {v:(GoodIndexTwo input x target)| v == i} @-}
castGoodIndexRight target input x i  = cast (subStringConcat input x (stringLen target) i) i


-------------------------------------------------------------------------------
----------  Indices' Generation -----------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect makeIndices @-}
makeIndices :: SMTString -> SMTString -> Int -> Int -> List Int 
{-@ makeIndices :: input:SMTString -> target:SMTString -> lo:Nat -> hi:Int -> List (GoodIndex input target) 
  / [hi - lo] @-}
makeIndices input target lo hi 
  | hi < lo 
  = N
  | lo == hi, isGoodIndex input target lo
  = lo `C` N
  | lo == hi 
  = N
makeIndices input target lo hi 
  | isGoodIndex input target lo
  = lo `C` (makeIndices input target (lo + 1) hi)
  | otherwise 
  =    makeIndices input target (lo + 1) hi 

{-@ reflect isGoodIndex @-}
isGoodIndex :: SMTString -> SMTString -> Int -> Bool 
{-@ isGoodIndex :: input:SMTString -> target:SMTString -> i:Int 
  -> {b:Bool | Prop b <=> IsGoodIndex input target i} @-}
isGoodIndex input target i 
  =  subString input i (stringLen target)  == target  
  && i + stringLen target <= stringLen input
  && 0 <= i    


-------------------------------------------------------------------------------
----------  List Structure ----------------------------------------------------
-------------------------------------------------------------------------------
   
data List a = N | C a (List a) deriving (Show, Eq)
{-@ data List [llen] a 
  = N | C {lhead :: a , ltail :: List a} @-}


{-@ measure llen @-}
{-@ llen :: List a -> Nat @-} 
llen :: List a -> Int 
llen N        = 0 
llen (C _ xs) = 1 + llen xs 

{-@ reflect map @-}
{-@ map :: (a -> b) -> is:List a -> {os:List b | llen is == llen os} @-}
map :: (a -> b) -> List a -> List b
map _ N        = N
map f (C x xs) = C (f x) (map f xs)

{-@ reflect append @-}
append :: List a -> List a -> List a 
append N        ys = ys 
append (C x xs) ys = x `C` (append xs ys)


{-@ reflect chunk @-}
{-@ chunk :: i:Int -> xs:List a -> {v:List (List a) | if (i <= 1 || llen xs <= i) then (llen v == 1) else (llen v < llen xs) } / [llen xs] @-}
chunk :: Int -> List a -> List (List a)
chunk i xs 
  | i <= 1
  = C xs N 
  | llen xs <= i 
  = C xs N 
  | otherwise
  = C (take i xs) (chunk i (drop i xs))

{-@ reflect drop @-}
{-@ drop :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == llen xs - i } @-} 
drop :: Int -> List a -> List a 
drop i N = N 
drop i (C x xs)
  | i == 0 
  = C x xs  
  | otherwise 
  = drop (i-1) xs 

{-@ reflect take @-}
{-@ take :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == i} @-} 
take :: Int -> List a -> List a 
take i N = N 
take i (C x xs)
  | i == 0 
  = N  
  | otherwise 
  = C x (take (i-1) xs)


-------------------------------------------------------------------------------
----------  String Chunking ---------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect chunkString @-}
{-@ chunkString :: Int -> xs:SMTString -> List (SMTString) / [stringLen xs] @-}
chunkString :: Int -> SMTString -> List (SMTString)
chunkString i xs 
  | i <= 0 
  = C xs N 
  | stringLen xs <= i 
  = C xs N 
  | otherwise
  = C (takeString i xs) (chunkString i (dropString i xs))


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
------------ Liquid Proofs Start HERE -----------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
----------  Proof that toMI distributes ---------------------------------------
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
----------  Proof that MI is a Monoid -----------------------------------------
-------------------------------------------------------------------------------

mempty_left :: forall (target :: Symbol). (KnownSymbol target) => MI target -> Proof
{-@ mempty_left :: xs:MI target -> {mappend xs mempty == xs } @-}
mempty_left (MI i1 is1) 
  = let tg = fromString (symbolVal (Proxy :: Proxy target)) in 
      mappend (MI i1 is1) (mempty :: MI target)
  ==. mappend (MI i1 is1) (MI stringEmp N) 
  ==. MI (concatString i1 stringEmp)
         ((castGoodIndexRightList tg i1 stringEmp is1
            `append`
           makeNewIndices i1 stringEmp tg 
         ) `append`
         (map (shiftStringRight tg i1 stringEmp) N))
      ? concatStringNeutral i1 
        -- NV ordering is important! 
        -- concatString i1 stringEmp == i1 should come before application of MI
  ==. MI i1
         ((castGoodIndexRightList tg i1 stringEmp is1
            `append`
           makeNewIndices i1 stringEmp tg
         ) `append`
         (map (shiftStringRight tg i1 stringEmp) N))
  ==. MI i1 ((is1 `append` N) `append` (map (shiftStringRight tg i1 stringEmp) N))
      ? makeNewIndicesNullLeft i1 tg 
  ==. MI i1 (is1 `append` map (shiftStringRight tg i1 stringEmp) N)
      ? appendNil is1  
  ==. MI i1 (is1 `append` N)
      ? appendNil is1  
  ==. MI i1 is1 
  *** QED 

mempty_right :: forall (target :: Symbol). (KnownSymbol target) => MI target -> Proof
{-@ mempty_right :: xs:MI target -> {mappend mempty xs == xs } @-}
mempty_right (MI i is)
  =   let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      mappend (mempty :: MI target) (MI i is) 
  ==. mappend (MI stringEmp N) (MI i is) 
  ==. MI (concatString stringEmp i)
       ((castGoodIndexRightList tg stringEmp i N
          `append`
        makeNewIndices stringEmp i tg 
       ) `append`
       (map (shiftStringRight tg stringEmp i) is)) 
       ? concatStringNeutralRight i
  ==. MI i
        ((N`append` makeNewIndices stringEmp i tg
        ) `append`
        (map (shiftStringRight tg stringEmp i) is)) 
  ==. MI i
       (makeNewIndices stringEmp i tg
        `append`
       (map (shiftStringRight tg stringEmp i) is)) 
  ==. MI i (N `append` (map (shiftStringRight tg stringEmp i) is)) 
       ? makeNewIndicesNullRight i tg
  ==. MI i (map (shiftStringRight tg stringEmp i) is)
       ? mapShiftZero tg i is 
  ==. MI i is 
  *** QED 

{-@ mappend_assoc 
  :: x:MI target -> y:MI target -> z:MI target
  -> {v:Proof | mappend x (mappend y z) = mappend (mappend x y) z}
  @-}
mappend_assoc 
     :: forall (target :: Symbol). (KnownSymbol target) 
     => MI target ->  MI target ->  MI target -> Proof
mappend_assoc x@(MI xi xis) y@(MI yi yis) z@(MI zi zis)
  | stringLen (fromString (symbolVal (Proxy :: Proxy target))) <= stringLen yi 
  = let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      mappend x (mappend y z)
  ==. mappend (MI xi xis) (mappend (MI yi yis) (MI zi zis))
  ==. mappend (MI xi xis) 
              (MI (concatString yi zi)
                  ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis)))
  ==. MI (concatString xi (concatString yi zi))
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis))))
      ? concatStringAssoc xi yi zi 
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis))))
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? mapAppend (shiftStringRight tg xi (concatString yi zi))
                  (castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   )
                   (map (shiftStringRight tg yi zi) zis)
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis)
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? mapAppend (shiftStringRight tg xi (concatString yi zi))
                  (castGoodIndexRightList tg yi zi yis)
                  (makeNewIndices yi zi tg)
-- ((x1~x2) ~ (x3~x4)) ~ x5
-- == 
-- (x1~x2) ~ x3 ~ x4 ~ x5 

  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? appendReorder (castGoodIndexRightList tg xi (concatString yi zi) xis)
                      (makeNewIndices xi (concatString yi zi) tg)
                      (map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis))
                      (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
                      (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))

  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis) 
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? castEq1 tg xi yi zi xis 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
           `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
          ) `append`
          map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? shiftIndexesLeft xi yi zi tg 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
           `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
          ) `append`
          castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
         ? castEq3 tg xi yi zi yis 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
           `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
          ) `append`
          castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis))
            `append`
           makeNewIndices (concatString xi yi) zi tg
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
         ? shiftIndexesRight xi yi zi tg 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
           `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
          ) `append`
          castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis))
            `append`
           makeNewIndices (concatString xi yi) zi tg
           )
            `append`
           map (shiftStringRight tg (concatString xi yi) zi) zis)
         ? mapLenFusion tg xi yi zi zis 
  ==. MI (concatString (concatString xi yi) zi)
         (((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
              `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
           ) `append`
           castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis)
            `append`
          makeNewIndices (concatString xi yi) zi tg
          ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
        ? castAppend tg (concatString xi yi) zi 
                     (castGoodIndexRightList tg xi yi xis)
                     (makeNewIndices xi yi tg)
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis)
            `append`
          makeNewIndices (concatString xi yi) zi tg
         ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
        ? castAppend tg (concatString xi yi) zi 
             (castGoodIndexRightList tg xi yi xis
              `append`
             makeNewIndices xi yi tg
             )
             (map (shiftStringRight tg xi yi) yis)
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg (concatString xi yi) zi ((castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           (map (shiftStringRight tg xi yi) yis))
            `append`
          makeNewIndices (concatString xi yi) zi tg
         ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
  ==. mappend (
        MI (concatString xi yi)
           ((castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           (map (shiftStringRight tg xi yi) yis))) (MI zi zis) 
  ==. mappend (mappend (MI xi xis) (MI yi yis)) (MI zi zis)
  *** QED 


-------------------------------------------------------------------------------
----------  Lemmata on Casts --------------------------------------------------
-------------------------------------------------------------------------------

{-@ castAppend :: target:SMTString -> input:SMTString -> x:SMTString 
     -> is1:List (GoodIndex input target) 
     -> is2:List (GoodIndex input target) -> 
   {castGoodIndexRightList target input x (append is1 is2) == append (castGoodIndexRightList target input x is1) (castGoodIndexRightList target input x is2)}
    @-}
castAppend :: SMTString -> SMTString -> SMTString -> List Int -> List Int -> Proof 
castAppend target input x is1 is2 
  =   castGoodIndexRightList target input x (append is1 is2)
  ==. append is1 is2 
  ==. append (castGoodIndexRightList target input x is1) (castGoodIndexRightList target input x is2)
  *** QED 

castEq1 :: SMTString -> SMTString -> SMTString -> SMTString -> List Int -> Proof
{-@ castEq1 :: tg:SMTString -> xi:SMTString -> yi:SMTString -> zi:SMTString 
             ->  xis:List (GoodIndex xi tg) 
        -> {castGoodIndexRightList tg xi (concatString yi zi) xis == castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)} @-}
castEq1 tg xi yi zi xis 
  =   castGoodIndexRightList tg xi (concatString yi zi) xis
  ==. xis 
  ==. castGoodIndexRightList tg xi yi xis
  ==. castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
  *** QED 


castEq3 :: SMTString -> SMTString -> SMTString -> SMTString -> List Int -> Proof
{-@ castEq3 :: tg:SMTString -> xi:SMTString -> yi:SMTString -> zi:SMTString 
             ->  yis:List (GoodIndex yi tg) 
        -> {castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis) == map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis)} @-}
castEq3 tg xi yi zi yis 
  =   castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis)
  ==. map (shiftStringRight tg xi yi) yis 
  ==. map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis)
        ? mapShiftIndex tg xi yi zi yis 
  *** QED 


-------------------------------------------------------------------------------
----------  Lemmata on Lists --------------------------------------------------
-------------------------------------------------------------------------------

{-@ appendNil :: xs:List a -> { append xs N = xs } @-} 
appendNil :: List a -> Proof 
appendNil N 
  =   append N N
  ==. N
  *** QED 
appendNil (C x xs) 
  =   append (C x xs) N
  ==. C x (append xs N)
  ==. C x xs ? appendNil xs 
  *** QED 

appendReorder :: List a -> List a -> List a -> List a -> List a -> Proof
{-@ appendReorder 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> x5:List a 
  -> {   (append (append x1 x2) (append (append x3 x4) x5))
      == (append (append (append (append x1 x2) x3) x4) x5)
     } @-}
appendReorder x1 x2 x3 x4 x5 
  =   append (append x1 x2) (append (append x3 x4) x5)
  ==. append (append x1 x2) (append x3 (append x4 x5))
       ? appendAssoc x3 x4 x5 
  ==. append (append (append x1 x2) x3) (append x4 x5)
      ? appendAssoc (append x1 x2) x3 (append x4 x5) 
  ==. append ((append (append (append x1 x2) x3)) x4) x5
      ? appendAssoc (append (append x1 x2) x3) x4 x5 
  *** QED 

{-@ appendAssoc :: x:List a -> y:List a -> z:List a 
     -> {(append x (append y z)) == (append (append x y) z) } @-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc N y z 
  =   append N (append y z)
  ==. append y z
  ==. append (append N y) z
  *** QED 
appendAssoc (C x xs) y z
  =   append (C x xs) (append y z) 
  ==. C x (append xs (append y z))
  ==. C x (append (append xs y) z)
        ? appendAssoc xs y z
  ==. append (C x (append xs y)) z
  ==. append (append (C x xs) y) z
  *** QED 


mapAppend :: (a -> b) -> List a -> List a -> Proof
{-@ mapAppend 
     :: f:(a -> b) -> xs:List a -> ys:List a 
     -> {map f (append xs ys) == append (map f xs) (map f ys)}
  @-}
mapAppend f N ys 
  =   map f (append N ys)
  ==. map f ys 
  ==. append N (map f ys)
  ==. append (map f N) (map f ys)
  *** QED 
mapAppend f (C x xs) ys 
  =   map f (append (C x xs) ys)
  ==. map f (x `C` (append xs ys))
  ==. f x `C` (map f (append xs ys))
  ==. f x `C` (append (map f xs) (map f ys))
      ? mapAppend f xs ys 
  ==. append (f x `C` map f xs) (map f ys)
  ==. append (map f (x `C` xs)) (map f ys)
  *** QED 


-------------------------------------------------------------------------------
----------  Lemmata on Empty Indices ------------------------------------------
-------------------------------------------------------------------------------

makeNewIndicesNullLeft :: SMTString -> SMTString -> Proof 
{-@ makeNewIndicesNullLeft 
  :: s:SMTString 
  -> t:SMTString 
  -> {makeNewIndices s stringEmp t == N } @-} 
makeNewIndicesNullLeft s t 
  | stringLen t < 2 
  = makeNewIndices s stringEmp t ==. N *** QED 
makeNewIndicesNullLeft  s t 
  | 1 + stringLen s <= stringLen t
  =   makeNewIndices s stringEmp t
  ==. makeIndices (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndices s t
                   0
                   (stringLen s - 1) 
                   ? concatStringNeutral s
  ==. makeIndices s t
                   0
                   (stringLen s - 1)
  ==. N ? makeNewIndicesNullSmallInput s t 0 (stringLen s - 1)
  *** QED 
makeNewIndicesNullLeft s t 
  =   makeNewIndices s stringEmp t
  ==. makeIndices (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndices (concatString s stringEmp) t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1)
  ==. makeIndices s t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1) ? concatStringNeutral s 
  ==. N ? makeNewIndicesNullSmallIndex s t (1 + stringLen s - stringLen t) (stringLen s - 1)
  *** QED 

makeNewIndicesNullSmallInput :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeNewIndicesNullSmallInput 
  :: s:SMTString 
  -> t:{SMTString | 1 + stringLen s <= stringLen t } 
  -> lo:Nat 
  -> hi:Int
  -> {makeIndices s t lo hi == N } / [hi - lo] @-} 
makeNewIndicesNullSmallInput s1 t lo hi
  | hi < lo 
  = makeIndices s1 t lo hi ==. N *** QED 
  | lo == hi, not (isGoodIndex s1 t lo)
  = makeIndices s1 t lo hi ==. N *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeNewIndicesNullSmallInput s1 t (lo+1) hi
  *** QED 


makeNewIndicesNullSmallIndex :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeNewIndicesNullSmallIndex 
  :: s:SMTString 
  -> t:{SMTString | stringLen t < 2 + stringLen s } 
  -> lo:{Nat | 1 + stringLen s - stringLen t <= lo  } 
  -> hi:{Int | lo <= hi}
  -> {makeIndices s t lo hi == N } / [hi - lo] @-} 
makeNewIndicesNullSmallIndex s1 t lo hi
  | lo == hi, not (isGoodIndex s1 t lo)
  = makeIndices s1 t lo hi ==. N *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeNewIndicesNullSmallIndex s1 t (lo+1) hi
  *** QED 


makeNewIndicesNullRight :: SMTString -> SMTString -> Proof 
{-@ makeNewIndicesNullRight 
  :: s1:SMTString 
  -> t:SMTString 
  -> {makeNewIndices stringEmp s1 t == N } @-} 
makeNewIndicesNullRight s t 
  | stringLen t < 2 
  = makeNewIndices stringEmp s t  ==. N *** QED 
makeNewIndicesNullRight s t 
  =   makeNewIndices stringEmp s t
  ==. makeIndices (concatString stringEmp s) t
                   (maxInt (1 + stringLen stringEmp - stringLen t) 0)
                   (stringLen stringEmp - 1)
  ==. makeIndices s t
                   (maxInt (1 - stringLen t) 0)
                   (-1)
      ? concatStringNeutralRight s 
  ==. makeIndices s t 0 (-1)
  ==. N  
  *** QED

-------------------------------------------------------------------------------
----------  Lemmata on Shifting Indices ---------------------------------------
-------------------------------------------------------------------------------

mapLenFusion :: SMTString -> SMTString -> SMTString -> SMTString -> List Int -> Proof
{-@ mapLenFusion :: tg:SMTString -> xi:SMTString -> yi:SMTString -> zi:SMTString 
            -> zis:List (GoodIndex zi tg) 
        -> {map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis) == map (shiftStringRight tg (concatString xi yi) zi) zis} 
        / [llen zis ] @-}
mapLenFusion tg xi yi zi N  
  =   map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) N)
  ==. map (shiftStringRight tg xi (concatString yi zi)) N 
  ==. N 
  ==. map (shiftStringRight tg (concatString xi yi) zi) N 
  *** QED  
mapLenFusion tg xi yi zi (C i is)  
  =   map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) (C i is))
  ==. map (shiftStringRight tg xi (concatString yi zi)) (shiftStringRight tg yi zi i `C` map (shiftStringRight tg yi zi) is)
  ==. shiftStringRight tg xi (concatString yi zi) (shiftStringRight tg yi zi i) `C` (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) is))
  ==. shiftStringRight tg (concatString xi yi) zi i `C` (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) is))
  ==. shiftStringRight tg (concatString xi yi) zi i `C` (map (shiftStringRight tg (concatString xi yi) zi) is)
       ? mapLenFusion tg xi yi zi is 
  ==. map (shiftStringRight tg (concatString xi yi) zi) (C i is)
  *** QED  

{-@ shiftIndexesRight
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> { map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg) == makeNewIndices (concatString xi yi) zi tg }
  @-}
shiftIndexesRight :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices (concatString xi yi) zi tg 
  ==. N
  ==. map (shiftStringRight tg xi (concatString yi zi)) N
  ==. map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
  *** QED 
shiftIndexesRight xi yi zi tg
-- NV NV NV 
-- This is suspicious!!! it should require exactly the precondition 
-- || tg || <= || yi || 
--   | stringLen tg  <= stringLen yi + 1 
  =   makeNewIndices (concatString xi yi) zi tg  
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen (concatString xi yi) - (stringLen tg -1)) 0)
                   (stringLen (concatString xi yi) - 1 )
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (stringLen (concatString xi yi) - (stringLen tg -1))
                   (stringLen (concatString xi yi) - 1 )
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
  ==. makeIndices (concatString xi (concatString yi zi)) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
       ?concatStringAssoc xi yi zi
  ==. map (shiftStringRight tg xi (concatString yi zi)) (makeIndices (concatString yi zi) tg (stringLen yi - stringLen tg + 1) (stringLen yi - 1))
       ? shiftIndexesRight' (stringLen yi - stringLen tg + 1)
                            (stringLen yi - 1)
                            xi 
                            (concatString yi zi)
                            tg 
  ==. map (shiftStringRight tg xi (concatString yi zi)) 
               (makeIndices (concatString yi zi) tg 
                             (maxInt (stringLen yi - (stringLen tg -1)) 0)
                             (stringLen yi -1))
  ==. map (shiftStringRight tg xi (concatString yi zi)) 
          (makeNewIndices yi zi tg)
  *** QED

{-@ shiftIndexesRight'
  :: lo:Nat 
  -> hi:Int  
  -> x:SMTString 
  -> input:SMTString 
  -> target:SMTString
  -> { map (shiftStringRight target x input) (makeIndices input target lo hi) == makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi) }
  / [if hi < lo then 0 else  hi-lo]
  @-}
shiftIndexesRight' :: Int -> Int -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight' lo hi x input target
  | hi < lo 
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) N
  ==. N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
  *** QED 
  | lo == hi, isGoodIndex input target lo 
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (lo `C` N)
  ==. (shiftStringRight target x input lo) `C` (map (shiftStringRight target x input) N)
  ==. (stringLen x + lo) `C` N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIndexConcatFront input x target lo  -- ( => IsGoodIndex (concatString x input) target (stringLen x + lo))
  *** QED 
  | lo == hi
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) N
  ==. N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 

shiftIndexesRight' lo hi x input target
  | isGoodIndex input target lo
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (lo `C` makeIndices input target (lo+1) hi)
  ==. (shiftStringRight target x input lo) `C` (map (shiftStringRight target x input) (makeIndices input target (lo+1) hi))
  ==. (shift (stringLen x) lo) `C` (makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi))
      ? shiftIndexesRight' (lo+1) hi x input target
  ==. (stringLen x + lo) `C` (makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi))
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 
  | otherwise
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (makeIndices input target (lo + 1) hi)
  ==. makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi)
      ? shiftIndexesRight' (lo+1) hi x input target
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 


{-@ shiftIndexesLeft
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> {  makeNewIndices xi (concatString yi zi) tg == castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)}
  @-}
shiftIndexesLeft :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesLeft xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices xi (concatString yi zi) tg 
  ==. N
  ==. makeNewIndices xi yi tg 
  ==. castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
  *** QED 
  | otherwise
  =   makeNewIndices xi (concatString yi zi) tg 
  ==. makeIndices (concatString xi (concatString yi zi)) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
     ?concatStringAssoc xi yi zi 
  ==. makeIndices (concatString xi yi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)                
      ? concatmakeNewIndices (maxInt (stringLen xi - (stringLen tg-1)) 0) (stringLen xi - 1) tg (concatString xi yi) zi 
  ==. makeNewIndices xi yi tg 
  ==. castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
  *** QED 

{-@ concatmakeNewIndices
  :: lo:Nat -> hi:Int
  -> target: SMTString
  -> input : {SMTString | hi + stringLen target <= stringLen input } 
  -> input': SMTString   
  -> {  makeIndices (concatString input input') target lo hi == makeIndices input target lo hi }
  / [hi - lo]  @-}
concatmakeNewIndices :: Int -> Int -> SMTString -> SMTString -> SMTString  -> Proof
concatmakeNewIndices lo hi target input input'
  | hi < lo 
  =   makeIndices input target lo hi
  ==. N
  ==. makeIndices (concatString input input') target lo hi 
  *** QED 
  | lo == hi, isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` N
  ==. makeIndices (concatString input input') target lo hi 
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | lo == hi
  =  makeIndices input target lo hi 
  ==. N
  ==. makeIndices (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
concatmakeNewIndices lo hi target input input' 
  | isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` (makeIndices input target (lo + 1) hi)
  ==. lo `C` (makeIndices (concatString input input') target (lo + 1) hi)
       ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | otherwise 
  =   makeIndices input target lo hi
  ==. makeIndices input target (lo + 1) hi
  ==. makeIndices (concatString input input') target (lo + 1) hi
       ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 



{-@ isGoodIndexConcatFront 
  :: input:SMTString -> input':SMTString -> tg:SMTString -> i:Nat
  -> {((isGoodIndex input tg i) <=> isGoodIndex (concatString input' input) tg (stringLen input' + i) )
     } @-}
isGoodIndexConcatFront :: SMTString -> SMTString -> SMTString -> Int -> Proof 
isGoodIndexConcatFront input input' tg i 
  =   isGoodIndex input tg i 
  ==. (subString input i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)  
  ==. (subString input i (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen (concatString input' input) 
      && 0 <= i)  
  ==. (subString (concatString input' input) (stringLen input' + i) (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen (concatString input' input) 
      && 0 <= (stringLen input' + i))  
      ? (subStringConcatFront input input' (stringLen tg) i *** QED)
  ==. isGoodIndex (concatString input' input) tg (stringLen input' + i) 
  *** QED 


{-@ isGoodIndexConcatString 
  :: input:SMTString -> input':SMTString -> tg:SMTString -> i:{Int | i + stringLen tg <= stringLen input }
  -> {((isGoodIndex input tg i) <=> isGoodIndex (concatString input input') tg i)
     } @-}
isGoodIndexConcatString :: SMTString -> SMTString -> SMTString -> Int -> Proof 
isGoodIndexConcatString input input' tg i 
  =   isGoodIndex input tg i 
  ==. (subString input i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input
      && 0 <= i) 
  ==. (subString (concatString input input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)   
      ? (subStringConcat input input' (stringLen tg) i *** QED )
  ==. (subString (concatString input input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen (concatString input input') 
      && 0 <= i)   
      ? (((stringLen input <= stringLen (concatString input input') *** QED ) &&& (lenConcat input input') *** QED))
  ==. isGoodIndex (concatString input input') tg i 
  *** QED 


mapShiftZero :: SMTString -> SMTString -> List Int -> Proof
{-@ mapShiftZero :: target:SMTString -> i:SMTString -> is:List (GoodIndex i target) 
  -> {map (shiftStringRight target stringEmp i) is == is } 
  / [llen is] @-}
mapShiftZero target i N
  =   map (shiftStringRight target stringEmp i) N ==. N *** QED  
mapShiftZero target i (C x xs)
  =   map (shiftStringRight target stringEmp i) (C x xs) 
  ==. shiftStringRight target stringEmp i x `C` map (shiftStringRight target stringEmp i) xs
  ==. shift (stringLen stringEmp) x `C` map (shiftStringRight target stringEmp i) xs
  ==. shift 0 x `C` map (shiftStringRight target stringEmp i) xs
  ==. x `C` map (shiftStringRight target stringEmp i) xs
  ==. x `C` xs ? mapShiftZero target i xs 
  *** QED 


{-@ mapShiftIndex :: tg:SMTString -> xi:SMTString -> yi:SMTString -> zi:SMTString -> xs:List (GoodIndex yi tg)
  -> {map (shiftStringRight tg xi yi) xs == map (shiftStringRight tg xi (concatString yi zi)) xs} / [llen xs] @-}
mapShiftIndex :: SMTString -> SMTString -> SMTString -> SMTString -> List Int -> Proof
mapShiftIndex tg xi yi zi N 
  = map (shiftStringRight tg xi yi) N ==. N ==. map (shiftStringRight tg xi (concatString yi zi)) N *** QED 
  *** QED 
mapShiftIndex tg xi yi zi zs@(C i0 is0)
  =   let is = castGoodIndexRightList tg yi zi is0 
          i  = castGoodIndexRight     tg yi zi i0  in 
      map (shiftStringRight tg xi yi) (C i is) 
  ==. C (shiftStringRight tg xi yi i) (map (shiftStringRight tg xi yi) is)
  ==. C (shift (stringLen xi) i) (map (shiftStringRight tg xi yi) is)
  ==. C (shiftStringRight tg xi (concatString yi zi) i) (map (shiftStringRight tg xi yi) is)
  ==. C (shiftStringRight tg xi (concatString yi zi) i) (map (shiftStringRight tg xi (concatString yi zi)) is)
       ? mapShiftIndex tg xi yi zi is
  ==. map (shiftStringRight tg xi (concatString yi zi)) (C i is)
  *** QED 

