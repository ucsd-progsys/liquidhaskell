module Plot where

import Text.Printf ( printf )
import Control.Lens ( _Just, (.~) )
import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Diagrams
import Data.Default.Class (Default(..))
import Data.Colour ( opaque, withOpacity )
import Data.Colour.Names ( green, grey, red )

import Benchmark

chart :: Bool -> String -> BenchmarkDataSet -> Renderable (LayoutPick LogValue PlotIndex PlotIndex)
chart rev title bds = layoutToRenderable layout
 where
  layout =
      -- title + legend
        layout_title .~ title
      $ layout_title_style . font_size .~ 30
      $ layout_legend . _Just . legend_position .~ LegendAbove
      $ layout_legend . _Just . legend_margin .~ 10
      $ layout_legend . _Just . legend_label_style . font_size .~ 18

      -- X
      $ layout_x_axis . laxis_style . axis_grid_style .~ solidLine 0.4 (opaque grey)
      $ layout_x_axis . laxis_style . axis_label_gap .~ 3
      $ layout_x_axis . laxis_style . axis_label_style . font_size .~ 18
      $ layout_x_axis . laxis_override .~ axisGridAtBigTicks
      $ layout_top_axis_visibility . axis_show_line .~ True
      $ layout_top_axis_visibility . axis_show_ticks .~ True
      $ layout_top_axis_visibility . axis_show_labels .~ True
      $ layout_bottom_axis_visibility . axis_show_ticks .~ True

      -- Y
      $ layout_y_axis . laxis_generate .~ autoIndexAxis' True lab
      $ layout_y_axis . laxis_override .~ axisGridAtTicks
      $ layout_y_axis . laxis_reverse .~ True
      $ layout_y_axis . laxis_style . axis_grid_style .~ solidLine 0.5 (opaque grey)
      $ layout_y_axis . laxis_style . axis_label_style . font_size .~ 14
      $ layout_left_axis_visibility . axis_show_ticks .~ False

      -- data
      $ layout_plots .~ [ plotHBars bars ]

      $ def :: Layout LogValue PlotIndex

  bars = plot_bars_values_with_labels .~ addIndexes dat
      $ plot_bars_titles .~ ["","after","before"]
      $ plot_bars_style .~ BarsStacked
      $ plot_bars_spacing .~ BarsFixGap 10 10
      $ plot_bars_item_styles .~ colors
      $ plot_bars_label_bar_hanchor .~ BHA_Right
      $ plot_bars_label_bar_vanchor .~ BVA_Centre
      $ plot_bars_label_text_hanchor .~ HTA_Left
      $ plot_bars_label_text_vanchor .~ VTA_Centre
      $ plot_bars_label_offset .~ Vector 3 0
      $ plot_bars_label_style . font_slant .~ FontSlantItalic
      $ plot_bars_label_style . font_size .~ 15
      $ def

  (lab, dat) = diffData rev bds

  colors = map (\c -> (solidFillStyle $ withOpacity c 0.7, Nothing)) [grey, red, green]

-- TODO we currently ignore the test state flag
diffData :: Bool -> BenchmarkDataSet -> ([String], [[(LogValue, String)]])
diffData rev (BenchmarkDS rs xs as) =
  if rev
    then (alab ++ xlab ++ rlab, adat ++ xdat ++ rdat)
    else (rlab ++ xlab ++ alab, rdat ++ xdat ++ adat)
  where
  (rlab, rdat) = unzip $ map
    (\(l,(v, _)) -> (l, [ (LogValue 0, "")
                        , (LogValue 0, "")
                        , (LogValue v, printf "%0.2f" (-v)) ] )) rs
  (xlab, xdat) = unzip $ map
    (\(l,(a,_),(b,_)) -> (l, [ (LogValue (min a b), if a == b then "0.0" else "")
                             , if a < b then
                                   let v = b - a in
                                   (LogValue v, printf "%0.2f" v)
                                 else (LogValue 0, "")
                             , if b < a then
                                   let v = a - b in
                                   (LogValue v, printf "%0.2f" (-v))
                                 else (LogValue 0, "")
                             ] )) xs
  (alab, adat) = unzip $ map
    (\(l,(v,_)) -> (l, [ (LogValue 0, "")
                       , (LogValue v, printf "%0.2f" v)
                       , (LogValue 0, "") ] )) as

-- This is fitted to specific values above (font size etc)
heightHeuristic :: Int -> Double
heightHeuristic n | n < 10    = 8.0
                  | n < 28    = 9.0
                  | n < 65    = 10.0
                  | n < 138   = 11.0
                  | n < 283   = 12.0
                  | n < 577   = 13.0
                  | otherwise = 14.0

chartToFile :: Bool -> String -> BenchmarkDataSet -> FilePath -> IO ()
chartToFile rev title bds path =
  do let len = bdsLen bds
     let wh = (2048.0, 2.0 ** heightHeuristic len)
     let fo = FileOptions wh SVG loadSansSerifFonts
     let plot = chart rev title bds
     let cb = render plot wh
     putStrLn $ printf "Writing %s (%d entries, %.0fx%.0f)" path len (fst wh) (snd wh)
     _ <- cBackendToFile fo cb path
     pure ()
