{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.HsColour.Colourise
  ( module Language.Haskell.HsColour.ColourHighlight
  , ColourPrefs(..)
  , readColourPrefs
  , defaultColourPrefs
  , colourise
  ) where

{-@ LIQUID "--totality" @-}

import Language.Haskell.HsColour.ColourHighlight
import Language.Haskell.HsColour.Classify (TokenType(..))

import System.IO (hPutStrLn,stderr)
import System.Environment (getEnv)
import Data.List
import Prelude hiding (catch)
import Control.Exception.Base (catch)

-- | Colour preferences.
data ColourPrefs = ColourPrefs
  { keyword, keyglyph, layout, comment
  , conid, varid, conop, varop
  , string, char, number, cpp
  , selection, variantselection, definition :: [Highlight]
  } deriving (Eq,Show,Read)

defaultColourPrefs = ColourPrefs
  { keyword  = [Foreground Green,Underscore]
  , keyglyph = [Foreground Red]
  , layout   = [Foreground Cyan]
  , comment  = [Foreground Blue, Italic]
  , conid    = [Normal]
  , varid    = [Normal]
  , conop    = [Foreground Red,Bold]
  , varop    = [Foreground Cyan]
  , string   = [Foreground Magenta]
  , char     = [Foreground Magenta]
  , number   = [Foreground Magenta]
  , cpp      = [Foreground Magenta,Dim]
  , selection = [Bold, Foreground Magenta]
  , variantselection = [Dim, Foreground Red, Underscore]
  , definition = [Foreground Blue]
  }

-- NOTE, should we give a warning message on a failed reading?
parseColourPrefs :: String -> String -> IO ColourPrefs
parseColourPrefs file x =
    case reads x of
        (res,_):_ -> return res
        _ -> do hPutStrLn stderr ("Could not parse colour prefs from "++file
                                  ++": reverting to defaults")
                return defaultColourPrefs

-- | Read colour preferences from .hscolour file in the current directory, or failing that,
--   from \$HOME\/.hscolour, and failing that, returns a default set of prefs.
readColourPrefs :: IO ColourPrefs
readColourPrefs = catch
  (do val <- readFile ".hscolour"
      parseColourPrefs ".hscolour" val)
  (\ (_::IOError)-> catch
    (do home <- getEnv "HOME"
        val <- readFile (home++"/.hscolour")
        parseColourPrefs (home++"/.hscolour") val)
    (\ (_::IOError)-> return defaultColourPrefs))

-- | Convert token classification to colour highlights.
colourise :: ColourPrefs -> TokenType -> [Highlight]
colourise pref Space    = [Normal]
colourise pref Comment  = comment pref
colourise pref Keyword  = keyword pref
colourise pref Keyglyph = keyglyph pref
colourise pref Layout   = layout pref
colourise pref Conid    = conid pref
colourise pref Varid    = varid pref
colourise pref Conop    = conop pref
colourise pref Varop    = varop pref
colourise pref String   = string pref
colourise pref Char     = char pref
colourise pref Number   = number pref
colourise pref Cpp      = cpp pref
colourise pref Error    = selection pref
colourise pref Definition = definition pref

