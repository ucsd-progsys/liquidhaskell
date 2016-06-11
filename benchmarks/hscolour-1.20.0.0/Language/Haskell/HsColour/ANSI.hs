-- | Partially taken from Hugs AnsiScreen.hs library:
module Language.Haskell.HsColour.ANSI
  ( highlightOnG,highlightOn
  , highlightOff
  , highlightG,highlight
  , cleareol, clearbol, clearline, clearDown, clearUp, cls
  , goto
  , cursorUp, cursorDown, cursorLeft, cursorRight
  , savePosition, restorePosition
  , Highlight(..)
  , Colour(..)
  , colourCycle
  , enableScrollRegion, scrollUp, scrollDown
  , lineWrap
  , TerminalType(..)
  ) where

{-@ LIQUID "--totality" @-}

import Language.Haskell.HsColour.ColourHighlight
import Language.Haskell.HsColour.Output(TerminalType(..))

import Data.List (intersperse,isPrefixOf)
import Data.Char (isDigit)



-- Basic screen control codes:

type Pos           = (Int,Int)

at        :: Pos -> String -> String
-- | Move the screen cursor to the given position.
goto      :: Int -> Int -> String
home      :: String
-- | Clear the screen.
cls       :: String

at (x,y) s  = goto x y ++ s
goto x y    = '\ESC':'[':(show y ++(';':show x ++ "H"))
home        = goto 1 1

cursorUp    = "\ESC[A"
cursorDown  = "\ESC[B"
cursorRight = "\ESC[C"
cursorLeft  = "\ESC[D"

cleareol    = "\ESC[K"
clearbol    = "\ESC[1K"
clearline   = "\ESC[2K"
clearDown   = "\ESC[J"
clearUp     = "\ESC[1J"
-- Choose whichever of the following lines is suitable for your system:
cls         = "\ESC[2J"     -- for PC with ANSI.SYS
--cls         = "\^L"         -- for Sun window

savePosition    = "\ESC7"
restorePosition = "\ESC8"


-- data Colour    -- imported from ColourHighlight
-- data Highlight -- imported from ColourHighlight

instance Enum Highlight where
  fromEnum Normal       = 0
  fromEnum Bold         = 1
  fromEnum Dim          = 2
  fromEnum Underscore   = 4
  fromEnum Blink        = 5
  fromEnum ReverseVideo = 7
  fromEnum Concealed    = 8
  -- The translation of these depends on the terminal type, and they don't translate to single numbers anyway. Should we really use the Enum class for this purpose rather than simply moving this table to 'renderAttrG'?
  fromEnum (Foreground (Rgb _ _ _)) = error "Internal error: fromEnum (Foreground (Rgb _ _ _))"
  fromEnum (Background (Rgb _ _ _)) = error "Internal error: fromEnum (Background (Rgb _ _ _))"
  fromEnum (Foreground c) = 30 + fromEnum c
  fromEnum (Background c) = 40 + fromEnum c
  fromEnum Italic       = 2

  toEnum n = error $ "Internal error: toEnum " ++ show n ++ " on Highlight"

-- | = 'highlightG' 'Ansi16Colour'
highlight ::  [Highlight] -> String -> String
highlight = highlightG Ansi16Colour

-- | = 'highlightOn' 'Ansi16Colour'
highlightOn ::  [Highlight] -> String
highlightOn = highlightOnG Ansi16Colour


-- | Make the given string appear with all of the listed highlights
highlightG :: TerminalType -> [Highlight] -> String -> String
highlightG tt attrs s = highlightOnG tt attrs ++ s ++ highlightOff

{-@ highlightOnG :: TerminalType -> xs:[Highlight] -> String / [(if ((len xs) = 0) then 2 else (len xs))] @-}
highlightOnG :: TerminalType -> [Highlight] -> String
highlightOnG tt []     = highlightOnG tt [Normal]
highlightOnG tt attrs  = "\ESC["
                       ++ concat (intersperse ";" (concatMap (renderAttrG tt) attrs))
                       ++"m"
highlightOff ::  [Char]
highlightOff = "\ESC[0m"

renderAttrG ::  TerminalType -> Highlight -> [String]
renderAttrG XTerm256Compatible (Foreground (Rgb r g b)) = 
    [ "38", "5", show ( rgb24bit_to_xterm256 r g b ) ]
renderAttrG XTerm256Compatible (Background (Rgb r g b)) = 
    [ "48", "5", show ( rgb24bit_to_xterm256 r g b ) ]
renderAttrG _ a                                         = 
    [ show (fromEnum (hlProjectToBasicColour8 a)) ]

-- | An infinite supply of colours.
colourCycle :: [Colour]
colourCycle = cycle [Red,Blue,Magenta,Green,Cyan]


-- | Scrolling
enableScrollRegion :: Int -> Int -> String
enableScrollRegion start end = "\ESC["++show start++';':show end++"r"

scrollDown ::  String
scrollDown  = "\ESCD"
scrollUp ::  String
scrollUp    = "\ESCM"

-- Line-wrapping mode
lineWrap ::  Bool -> [Char]
lineWrap True  = "\ESC[7h"
lineWrap False = "\ESC[7l"

