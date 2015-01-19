{-# LANGUAGE ViewPatterns #-}
module InTex where

import Text.Pandoc.JSON
import Text.Pandoc
import Data.List
import Debug.Trace

main :: IO ()
main = toJSONFilter readFootnotes

-- gimme :: String -> String
gimme s = writeLaTeX def $ readMarkdown def s

readFootnotes :: Inline -> Inline
readFootnotes (footnoteText -> Just args) = RawInline (Format "tex") res
  where
    parsed   = writeLaTeX def . readMarkdown def
    res     = fnString ++ parsed args ++ "}"
    -- res      = trace (msg args res') res' 
    -- msg s s' = unlines ["Transforming:", s, "To:", s']

readFootnotes i = i

fnString = "\\footnotetext{"

footnoteText :: Inline -> Maybe String
footnoteText (RawInline (Format "tex") s) =
  if fnString `isPrefixOf` s
    then Just . init . drop (length fnString) $ s -- Remove closing brace
    else Nothing
footnoteText x = Nothing

