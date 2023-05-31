module Plot where

import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Diagrams
  (renderableToFile, FileFormat(..), FileOptions(..))
import Data.Default.Class (Default(..))
import Control.Lens ((.~))

chart'' :: Renderable ()
chart'' = toRenderable layout
  where
    layout = layout_title .~ "Time (seconds)"
           $ layout_title_style . font_size .~ 10
           $ layout_x_axis . laxis_generate .~ autoIndexAxis (map (\(n,_,_) -> n) dat)
           $ layout_y_axis . laxis_override .~ axisGridHide
           $ layout_left_axis_visibility . axis_show_ticks .~ True
           $ layout_plots .~ [ plotBars bars2 ]
           $ def :: Layout PlotIndex LogValue

    bars2 = plot_bars_titles .~ ["Before","After"]
        $ plot_bars_values .~ addIndexes (map (\(_,a,b) -> [LogValue $ min a b, LogValue $ abs (a-b)]) dat)
        $ plot_bars_style .~ BarsStacked
        $ plot_bars_spacing .~ BarsFixGap 5 5
        $ plot_bars_item_styles .~ map mkstyle (cycle defaultColorSeq)
        $ def :: PlotBars PlotIndex LogValue
    mkstyle c = (solidFillStyle c, Nothing)


    dat :: [(String, Double, Double)]
    dat = [("benchmarks/esop2013-submission/Base",50.494239,48.037624),
           ("pos/RBTree_col_height",2.8764499999999997,1.691758),
           ("pos/ListSort",1.81999,0.7128519999999999),
           ("benchmarks/vector-algorithms-0.5.4.2/Data/Vector/Algorithms/AmericanFlag",8.382626,7.340566),
           ("pos/GhcSort1",1.844271,0.935836),("pos/MapReduceVerified",5.71887,4.853692),
           ("benchmarks/bytestring-0.9.2.1/Data/ByteString/Fusion/T",31.111687999999997,30.406934),
           ("benchmarks/icfp15/pos/FoldAbs",6.113898,5.463777),
           ("pos/Pair",1.198364,0.562416),
           ("benchmarks/bytestring-0.9.2.1/Data/ByteString/Lazy",27.701095000000002,27.103975),
           ("benchmarks/icfp15/neg/DataBase",3.7489079999999997,3.1742600000000003),
           ("benchmarks/icfp15/pos/IfM",4.883421,4.365702000000001),
           ("pos/Map2",5.1833800000000005,4.779614),
           ("pos/StateConstraints",6.081063,5.704585),
           ("pos/Meas6",0.6448780000000001,0.29709399999999997),

           ("pos/T1649WorkTypes",0.384089,1.506924),
           ("pos/GCD",0.33426999999999996,1.085934),
           ("pos/Polyqual",0.483382,1.1766800000000002),
           ("pos/RBTree",6.192317,6.871176),
           ("pos/ReWrite8",2.7452669999999997,3.252186),
           ("pos/MergeSort_bag",0.47985099999999997,0.830577),
           ("pos/Meas2",0.262728,0.597352),
           ("pos/FingerTree",1.7555260000000001,1.975208),
           ("benchmarks/esop2013-submission/GhcListSort",3.781875,3.995183),
           ("import/lib/ReflectLib8",0.216977,0.42918900000000004),
           ("names/pos/Vector04",0.392394,0.5603619999999999),
           ("benchmarks/popl18/nople/pos/MapFusion",0.8483440000000001,1.009964),
           ("benchmarks/popl18/ple/pos/Solver",0.680353,0.826187),
           ("benchmarks/popl18/nople/neg/MonadList",1.328122,1.459384),
           ("benchmarks/esop2013-submission/Toy",0.555504,0.685884)
           ]

{-
chart' :: Bool -> Renderable ()
chart' borders = toRenderable layout
 where
  layout =
        layout_title .~ "Sample Bars" ++ btitle
      $ layout_title_style . font_size .~ 10
      $ layout_x_axis . laxis_generate .~ autoIndexAxis alabels
      $ layout_y_axis . laxis_override .~ axisGridHide
      $ layout_left_axis_visibility . axis_show_ticks .~ False
      $ layout_plots .~ [ plotBars bars2 ]
      $ def :: Layout PlotIndex Double

  bars2 = plot_bars_titles .~ ["Cash","Equity"]
      $ plot_bars_values .~ addIndexes [[20,45],[45,30],[30,20],[70,25]]
      $ plot_bars_style .~ BarsStacked
      $ plot_bars_spacing .~ BarsFixGap 30 5
      $ plot_bars_item_styles .~ map mkstyle (cycle defaultColorSeq)
      $ def

  alabels = [ "Jun", "Jul", "Aug", "Sep", "Oct" ]

  btitle = if borders then "" else " (no borders)"
  bstyle = if borders then Just (solidLine 1.0 $ opaque black) else Nothing
  mkstyle c = (solidFillStyle c, bstyle)

chart :: Renderable ()
chart = toRenderable layout
  where
    values = [ ("Mexico City",19.2,e), ("Mumbai",12.9,e)
             , ("Sydney",4.3,e), ("London",8.3,e), ("New York",8.2,e1) ]
    e = 0
    e1 = 25
    pitem (s,v,o) = pitem_value .~ v
                  $ pitem_label .~ s
                  $ pitem_offset .~ o
                  $ def

    layout = pie_title .~ "Relative Population"
           $ pie_plot . pie_data .~ map pitem values
           $ def
-}

main1 :: IO (PickFn ())
main1 = renderableToFile def{_fo_format=SVG_EMBEDDED} "example.svg" chart''

