module Plot where

import Text.Printf ( printf )
import Data.Either.Extra (fromEither)
import Control.Lens ( _Just, (.~) )
import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Diagrams
    ( cBackendToFile,
      loadSansSerifFonts,
      FileFormat(..),
      FileOptions(..))
import Data.Default.Class (Default(..))
import Data.Colour ( opaque, withOpacity )
import Data.Colour.Names ( green, grey, red )

import Benchmark

chart :: Bool -> String -> BenchmarkDataSet -> Renderable (LayoutPick LogValue PlotIndex PlotIndex)
chart rev title (BenchmarkDS rs xs as) = layoutToRenderable layout
 where
  layout =
      -- title + legend
        layout_title .~ title
      $ layout_title_style . font_size .~ 30
      $ layout_legend . _Just . legend_position .~ LegendAbove
      $ layout_legend . _Just . legend_margin .~ 10

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
      $ plot_bars_item_styles .~ map (\c -> (solidFillStyle $ withOpacity c 0.7, Nothing)) [grey, red, green]
      $ plot_bars_label_bar_hanchor .~ BHA_Right
      $ plot_bars_label_bar_vanchor .~ BVA_Centre
      $ plot_bars_label_text_hanchor .~ HTA_Left
      $ plot_bars_label_text_vanchor .~ VTA_Centre
      $ plot_bars_label_offset .~ Vector 3 0
      $ plot_bars_label_style . font_slant .~ FontSlantItalic
      $ plot_bars_label_style . font_size .~ 15
      $ def

  -- TODO we currently ignore the info about test state (via fromEither)
  (lab, dat) =
    let
      (rlab, rdat) = unzip $ map
        (\(l,d) -> let v = fromEither d in
                   (l, [ (LogValue 0, "")
                       , (LogValue 0, "")
                       , (LogValue v, printf "%0.2f" (-v)) ] )) rs
      (xlab, xdat) = unzip $ map
        (\(l,da,db) -> let a = fromEither da
                           b = fromEither db
                       in
                   (l, [ (LogValue (min a b), "")
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
        (\(l,d) -> let v = fromEither d in
                   (l, [ (LogValue 0, "")
                       , (LogValue v, printf "%0.2f" v)
                       , (LogValue 0, "") ] )) as
    in
      if rev
        then (alab ++ xlab ++ rlab, adat ++ xdat ++ rdat)
        else (rlab ++ xlab ++ alab, rdat ++ xdat ++ adat)

chartToFile :: Bool -> String -> BenchmarkDataSet -> FilePath -> IO ()
chartToFile rev title bds path =
  do let wh = (2048.0, 2048.0)
     let fo = FileOptions wh SVG loadSansSerifFonts
     let cb = render (chart rev title bds) wh
     _ <- cBackendToFile fo cb path
     pure ()
