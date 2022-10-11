-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.IO
-- Copyright   :  (c) Alberto Ruiz 2010
-- License     :  GPL
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable
--
-- Display, formatting and IO functions for numeric 'Vector' and 'Matrix'
--
-----------------------------------------------------------------------------

module Numeric.IO (
    dispf, disps, dispcf, vecdisp, latexFormat, format,
    loadMatrix, saveMatrix, fromFile, fileDimensions,
    readMatrix, fromArray2D,
    fscanfVector, fprintfVector, freadVector, fwriteVector
) where

import Data.Packed
import Data.Packed.Internal
import System.Process(readProcess)
import Text.Printf(printf)
import Data.List(intersperse)
import Data.Complex

{- | Creates a string from a matrix given a separator and a function to show each entry. Using
this function the user can easily define any desired display function:

@import Text.Printf(printf)@

@disp = putStr . format \"  \" (printf \"%.2f\")@

-}
format :: (Element t) => String -> (t -> String) -> Matrix t -> String
format sep f m = table sep . map (map f) . toLists $ m

{- | Show a matrix with \"autoscaling\" and a given number of decimal places.

@disp = putStr . disps 2

\> disp $ 120 * (3><4) [1..]
3x4  E3
 0.12  0.24  0.36  0.48
 0.60  0.72  0.84  0.96
 1.08  1.20  1.32  1.44
@
-}
disps :: Int -> Matrix Double -> String
disps d x = sdims x ++ "  " ++ formatScaled d x

{- | Show a matrix with a given number of decimal places.

@disp = putStr . dispf 3

\> disp (1/3 + ident 4)
4x4
1.333  0.333  0.333  0.333
0.333  1.333  0.333  0.333
0.333  0.333  1.333  0.333
0.333  0.333  0.333  1.333
@
-}
dispf :: Int -> Matrix Double -> String
dispf d x = sdims x ++ "\n" ++ formatFixed (if isInt x then 0 else d) x

sdims x = show (rows x) ++ "x" ++ show (cols x)

formatFixed d x = format "  " (printf ("%."++show d++"f")) $ x

isInt = all lookslikeInt . toList . flatten

formatScaled dec t = "E"++show o++"\n" ++ ss
    where ss = format " " (printf fmt. g) t
          g x | o >= 0    = x/10^(o::Int)
              | otherwise = x*10^(-o)
          o = floor $ maximum $ map (logBase 10 . abs) $ toList $ flatten t
          fmt = '%':show (dec+3) ++ '.':show dec ++"f"

{- | Show a vector using a function for showing matrices.

@disp = putStr . vecdisp ('dispf' 2)

\> disp ('linspace' 10 (0,1))
10 |> 0.00  0.11  0.22  0.33  0.44  0.56  0.67  0.78  0.89  1.00
@
-}
vecdisp :: (Element t) => (Matrix t -> String) -> Vector t -> String
vecdisp f v
    = ((show (dim v) ++ " |> ") ++) . (++"\n")
    . unwords . lines .  tail . dropWhile (not . (`elem` " \n"))
    . f . trans . reshape 1
    $ v

-- | Tool to display matrices with latex syntax.
latexFormat :: String -- ^ type of braces: \"matrix\", \"bmatrix\", \"pmatrix\", etc.
            -> String -- ^ Formatted matrix, with elements separated by spaces and newlines
            -> String
latexFormat del tab = "\\begin{"++del++"}\n" ++ f tab ++ "\\end{"++del++"}"
    where f = unlines . intersperse "\\\\" . map unwords . map (intersperse " & " . words) . tail . lines

-- | Pretty print a complex number with at most n decimal digits.
showComplex :: Int -> Complex Double -> String
showComplex d (a:+b)
    | isZero a && isZero b = "0"
    | isZero b = sa
    | isZero a && isOne b = s2++"i"
    | isZero a = sb++"i"
    | isOne b = sa++s3++"i"
    | otherwise = sa++s1++sb++"i"
  where
    sa = shcr d a
    sb = shcr d b
    s1 = if b<0 then "" else "+"
    s2 = if b<0 then "-" else ""
    s3 = if b<0 then "-" else "+"

shcr d a | lookslikeInt a = printf "%.0f" a
         | otherwise      = printf ("%."++show d++"f") a


lookslikeInt x = show (round x :: Int) ++".0" == shx || "-0.0" == shx
   where shx = show x

isZero x = show x `elem` ["0.0","-0.0"]
isOne  x = show x `elem` ["1.0","-1.0"]

-- | Pretty print a complex matrix with at most n decimal digits.
dispcf :: Int -> Matrix (Complex Double) -> String
dispcf d m = sdims m ++ "\n" ++ format "  " (showComplex d) m

--------------------------------------------------------------------

-- | reads a matrix from a string containing a table of numbers.
readMatrix :: String -> Matrix Double
readMatrix = fromLists . map (map read). map words . filter (not.null) . lines

{- |  obtains the number of rows and columns in an ASCII data file
      (provisionally using unix's wc).
-}
fileDimensions :: FilePath -> IO (Int,Int)
fileDimensions fname = do
    wcres <- readProcess "wc" ["-w",fname] ""
    contents <- readFile fname
    let tot = read . head . words $ wcres
        c   = length . head . dropWhile null . map words . lines $ contents
    if tot > 0
        then return (tot `div` c, c)
        else return (0,0)

-- | Loads a matrix from an ASCII file formatted as a 2D table.
loadMatrix :: FilePath -> IO (Matrix Double)
loadMatrix file = fromFile file =<< fileDimensions file

-- | Loads a matrix from an ASCII file (the number of rows and columns must be known in advance).
fromFile :: FilePath -> (Int,Int) -> IO (Matrix Double)
fromFile filename (r,c) = reshape c `fmap` fscanfVector filename (r*c)

