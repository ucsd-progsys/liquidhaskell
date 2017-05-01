-----------------------------------------------------------------------------
-- |
-- Module      :  Graphics.Plot
-- Copyright   :  (c) Alberto Ruiz 2005-8
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz (aruiz at um dot es)
-- Stability   :  provisional
-- Portability :  uses gnuplot and ImageMagick
--
-- This module is deprecated. It can be replaced by improved drawing tools
-- available in the plot\\plot-gtk packages by Vivian McPhail or Gnuplot by Henning Thielemann.
-----------------------------------------------------------------------------

module Graphics.Plot(

    mplot,

    plot, parametricPlot, 

    splot, mesh, meshdom,

    matrixToPGM, imshow,

    gnuplotX, gnuplotpdf, gnuplotWin

) where

import Numeric.Container
import Data.List(intersperse)
import System.Process (system)

-- | From vectors x and y, it generates a pair of matrices to be used as x and y arguments for matrix functions.
meshdom :: Vector Double -> Vector Double -> (Matrix Double , Matrix Double)
meshdom r1 r2 = (outer r1 (constant 1 (dim r2)), outer (constant 1 (dim r1)) r2)


{- | Draws a 3D surface representation of a real matrix.

> > mesh $ build (10,10) (\\i j -> i + (j-5)^2)

In certain versions you can interactively rotate the graphic using the mouse.

-}
mesh :: Matrix Double -> IO ()
mesh m = gnuplotX (command++dat) where
    command = "splot "++datafollows++" matrix with lines\n"
    dat = prep $ toLists m

{- | Draws the surface represented by the function f in the desired ranges and number of points, internally using 'mesh'.

> > let f x y = cos (x + y) 
> > splot f (0,pi) (0,2*pi) 50    

-}
splot :: (Matrix Double->Matrix Double->Matrix Double) -> (Double,Double) -> (Double,Double) -> Int -> IO () 
splot f rx ry n = mesh z where
    (x,y) = meshdom (linspace n rx) (linspace n ry)
    z = f x y

{- | plots several vectors against the first one 

> > let t = linspace 100 (-3,3) in mplot [t, sin t, exp (-t^2)]

-}
mplot :: [Vector Double] -> IO ()
mplot m = gnuplotX (commands++dats) where
    commands = if length m == 1 then command1 else commandmore
    command1 = "plot "++datafollows++" with lines\n" ++ dat
    commandmore = "plot " ++ plots ++ "\n"
    plots = concat $ intersperse ", " (map cmd [2 .. length m])
    cmd k = datafollows++" using 1:"++show k++" with lines"
    dat = prep $ toLists $ fromColumns m
    dats = concat (replicate (length m-1) dat)


{- | Draws a list of functions over a desired range and with a desired number of points 

> > plot [sin, cos, sin.(3*)] (0,2*pi) 1000

-}
plot :: [Vector Double->Vector Double] -> (Double,Double) -> Int -> IO ()
plot fs rx n = mplot (x: mapf fs x)
    where x = linspace n rx
          mapf gs y = map ($ y) gs

{- | Draws a parametric curve. For instance, to draw a spiral we can do something like:

> > parametricPlot (\t->(t * sin t, t * cos t)) (0,10*pi) 1000

-}
parametricPlot :: (Vector Double->(Vector Double,Vector Double)) -> (Double, Double) -> Int -> IO ()
parametricPlot f rt n = mplot [fx, fy]
    where t = linspace n rt
          (fx,fy) = f t


-- | writes a matrix to pgm image file
matrixToPGM :: Matrix Double -> String
matrixToPGM m = header ++ unlines (map unwords ll) where
    c = cols m
    r = rows m
    header = "P2 "++show c++" "++show r++" "++show (round maxgray :: Int)++"\n"
    maxgray = 255.0
    maxval = maxElement m
    minval = minElement m
    scale' = if maxval == minval
        then 0.0
        else maxgray / (maxval - minval)
    f x = show ( round ( scale' *(x - minval) ) :: Int )
    ll = map (map f) (toLists m)

-- | imshow shows a representation of a matrix as a gray level image using ImageMagick's display.
imshow :: Matrix Double -> IO ()
imshow m = do
    _ <- system $ "echo \""++ matrixToPGM m ++"\"| display -antialias -resize 300 - &"
    return ()

----------------------------------------------------

gnuplotX :: String -> IO ()
gnuplotX command = do { _ <- system cmdstr; return()} where
    cmdstr = "echo \""++command++"\" | gnuplot -persist"

datafollows = "\\\"-\\\""

prep = (++"e\n\n") . unlines . map (unwords . map show)


gnuplotpdf :: String -> String -> [([[Double]], String)] -> IO ()
gnuplotpdf title command ds = gnuplot (prelude ++ command ++" "++ draw) >> postproc where
    prelude = "set terminal epslatex color; set output '"++title++".tex';"
    (dats,defs) = unzip ds
    draw = concat (intersperse ", " (map ("\"-\" "++) defs)) ++ "\n" ++
           concatMap pr dats
    postproc = do
        _ <- system $ "epstopdf "++title++".eps"
        mklatex
        _ <- system $ "pdflatex "++title++"aux.tex > /dev/null"
        _ <- system $ "pdfcrop "++title++"aux.pdf > /dev/null"
        _ <- system $ "mv "++title++"aux-crop.pdf "++title++".pdf"
        _ <- system $ "rm "++title++"aux.* "++title++".eps "++title++".tex"
        return ()

    mklatex = writeFile (title++"aux.tex") $
       "\\documentclass{article}\n"++
       "\\usepackage{graphics}\n"++
       "\\usepackage{nopageno}\n"++
       "\\usepackage{txfonts}\n"++
       "\\renewcommand{\\familydefault}{phv}\n"++
       "\\usepackage[usenames]{color}\n"++

       "\\begin{document}\n"++

       "\\begin{center}\n"++
       "  \\input{./"++title++".tex}\n"++
       "\\end{center}\n"++

       "\\end{document}"

    pr = (++"e\n") . unlines . map (unwords . map show)

    gnuplot cmd = do
        writeFile "gnuplotcommand" cmd
        _ <- system "gnuplot gnuplotcommand"
        _ <- system "rm gnuplotcommand"
        return ()

gnuplotWin :: String -> String -> [([[Double]], String)] -> IO ()
gnuplotWin title command ds = gnuplot (prelude ++ command ++" "++ draw) where
    (dats,defs) = unzip ds
    draw = concat (intersperse ", " (map ("\"-\" "++) defs)) ++ "\n" ++
           concatMap pr dats

    pr = (++"e\n") . unlines . map (unwords . map show)

    prelude = "set title \""++title++"\";"

    gnuplot cmd = do
        writeFile "gnuplotcommand" cmd
        _ <- system "gnuplot -persist gnuplotcommand"
        _ <- system "rm gnuplotcommand"
        return ()
