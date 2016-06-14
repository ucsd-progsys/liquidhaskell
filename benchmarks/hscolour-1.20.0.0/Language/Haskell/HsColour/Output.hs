module Language.Haskell.HsColour.Output(TerminalType(..),Output(..)) where

{-@ LIQUID "--totality" @-}

data TerminalType = 
      Ansi16Colour -- ^ @\\033[Xm@-style escape sequences (with /X/ =~ [34][0-7]) 
    | XTerm256Compatible -- ^ 'Ansi16Colour', and also @\\033[Y8;5;Zm]@-style escape sequences (with /Y/ =~ [3,4] and /Z/ an integer in [0,255] with the XTerm colour cube semantics).
    deriving (Show,Eq,Ord)

-- | The supported output formats.
data Output = TTY   -- ^ ANSI terminal codes. Equivalent to 'TTYg' 'Ansi16Colour' but left in for backwards compatibility. 
            | TTYg TerminalType -- ^ Terminal codes appropriate for the 'TerminalType'.
            | LaTeX -- ^ TeX macros
            | HTML  -- ^ HTML with font tags
            | CSS   -- ^ HTML with CSS.
            | ACSS  -- ^ HTML with CSS and mouseover types. 
            | ICSS  -- ^ HTML with inline CSS.
            | MIRC  -- ^ mIRC chat clients
  deriving (Eq,Show)
