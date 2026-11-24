{-@ LIQUID "--expect-error-containing=someMeasure\nerrors" @-}
-- | Desugaring can only rename function parameters, and the parameters can only
-- be mentioned in local specifications. Therefore, the hint of "T2704" makes no
-- sense in the errors of this module.
--
-- The expected text is the end of the list of similar names, followed by the
-- location of the error, which leaves no room for the hint in between.
module T2704NoHint where

{-@ measure someMeasure :: Int -> Int @-}

-- Not a local specification
{-@ topLevel :: n:Int -> {v:Int | v = someMeasuer n} @-}
topLevel :: Int -> Int
topLevel n = n

-- Not a variable
constructor :: Int -> Int
constructor n = go n
  where
    {-@ go :: x:Int -> {v:Int | v = SomeMeasure x} @-}
    go :: Int -> Int
    go x = x

-- Not a parameter, because it is qualified
qualified :: Int -> Int
qualified n = go n
  where
    {-@ go :: x:Int -> {v:Int | v = Nowhere.someMeasure x} @-}
    go :: Int -> Int
    go x = x
