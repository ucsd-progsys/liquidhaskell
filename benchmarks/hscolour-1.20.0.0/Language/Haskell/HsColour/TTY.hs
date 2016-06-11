-- | Highlights Haskell code with ANSI terminal codes.
module Language.Haskell.HsColour.TTY (hscolour,hscolourG) where

{-@ LIQUID "--totality" @-}

import Language.Haskell.HsColour.ANSI as ANSI
import Language.Haskell.HsColour.Classify
import Language.Haskell.HsColour.Colourise
import Language.Haskell.HsColour.Output(TerminalType(Ansi16Colour))

-- | = 'hscolourG' 'Ansi16Colour'
hscolour :: ColourPrefs -- ^ Colour preferences.
         -> String      -- ^ Haskell source code.
         -> String      -- ^ Coloured Haskell source code.
hscolour = hscolourG Ansi16Colour

-- | Highlights Haskell code with ANSI terminal codes.
hscolourG terminalType pref = concatMap (renderTokenG terminalType pref) . tokenise


renderToken :: ColourPrefs -> (TokenType,String) -> String
renderToken = renderTokenG Ansi16Colour

renderTokenG terminalType pref (t,s) = ANSI.highlightG terminalType (colourise pref t) s
