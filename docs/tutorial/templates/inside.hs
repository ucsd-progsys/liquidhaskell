{-# LANGUAGE ViewPatterns #-}
module InTex where

import Text.Pandoc.JSON
import Text.Pandoc
import Data.List

main :: IO ()
main = toJSONFilter readFootnotes

readFootnotes :: Inline -> Inline
readFootnotes (footnoteText -> Just args) = RawInline (Format "tex") res
  where
    parsed = writeLaTeX def . readMarkdown def
    res = fnString ++ parsed args ++ "}"
readFootnotes i = i

fnString = "\\footnotetext{"

footnoteText :: Inline -> Maybe String
footnoteText (RawInline (Format "tex") s) =
  if fnString `isPrefixOf` s
    then Just . init . drop (length fnString) $ s -- Remove closing brace
    else Nothing
footnoteText x = Nothing
