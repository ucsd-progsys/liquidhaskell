-- | Formats Haskell source code using mIRC codes.
--   (see http:\/\/irssi.org\/documentation\/formats)
module Language.Haskell.HsColour.MIRC (hscolour) where

{-@ LIQUID "--totality" @-}

import Language.Haskell.HsColour.Classify as Classify
import Language.Haskell.HsColour.Colourise

import Data.Char(isAlphaNum)


-- | Formats Haskell source code using mIRC codes.
hscolour :: ColourPrefs -- ^ Colour preferences.
         -> String      -- ^ Haskell source code.
         -> String      -- ^ Coloured Haskell source code.
hscolour pref = concatMap (renderToken pref) . tokenise

renderToken :: ColourPrefs -> (TokenType,String) -> String
renderToken pref (t,s) = fontify (colourise pref t) s


-- mIRC stuff
fontify hs =
    mircColours (joinColours hs)
    . highlight (filterElts [Normal,Bold,Underscore,ReverseVideo] hs)
  where
    highlight [] s     = s
    highlight (h:hs) s = font h (highlight hs s)

    font Normal         s = s
    font Bold           s = '\^B':s++"\^B"
    font Underscore     s = '\^_':s++"\^_"
    font ReverseVideo   s = '\^V':s++"\^V"

{-@ qualif IsFont(v: Highlight): (isFont v) @-}

{-@ measure isFont :: Highlight -> Prop
    isFont(Normal) = true
    isFont(Bold) = true
    isFont(Underscore) = true
    isFont(ReverseVideo) = true
    isFont(Dim) = false
    isFont(Blink) = false
    isFont(Italic) = false
    isFont(Concealed) = false
    isFont(Background x) = false
    isFont(Foreground x) = false
  @-}

{-@ filterElts :: forall <p :: a -> Prop>. Eq a => [a<p>] -> [a] -> [a<p>] @-}
filterElts :: Eq a => [a] -> [a] -> [a]
filterElts xs ys = go xs xs ys


{-@ go :: forall <p :: a -> Prop>. Eq a => xs:[a<p>] -> ws:[a<p>] -> zs:[a] -> [a<p>] /[(len zs), (len ws)] @-}
go :: Eq a => [a] -> [a] -> [a] -> [a]
go xs (w:ws) (z:zs) | w == z    = z : go xs xs zs
                    | otherwise = go xs ws (z:zs)
go xs []     (z:zs)             = go xs xs zs
go xs ws     []                 = []

-- mIRC combines colour codes in a non-modular way
data MircColour = Mirc { fg::Colour, dim::Bool, bg::Maybe Colour, blink::Bool}

joinColours :: [Highlight] -> MircColour
joinColours = foldr join (Mirc {fg=Black, dim=False, bg=Nothing, blink=False})
  where
    join Blink           mirc = mirc {blink=True}
    join Dim             mirc = mirc {dim=True}
    join (Foreground fg) mirc = mirc {fg=fg}
    join (Background bg) mirc = mirc {bg=Just bg}
    join Concealed       mirc = mirc {fg=Black, bg=Just Black}
    join _               mirc = mirc

mircColours :: MircColour -> String -> String
mircColours (Mirc fg dim Nothing   blink) s = '\^C': code fg dim++s++"\^O"
mircColours (Mirc fg dim (Just bg) blink) s = '\^C': code fg dim++','
                                                   : code bg blink++s++"\^O"

{-@ code :: c:Colour -> Bool -> String / [ 1 - (isBasic c)] @-}
code :: Colour -> Bool -> String
code Black   False = "1"
code Red     False = "5"
code Green   False = "3"
code Yellow  False = "7"
code Blue    False = "2"
code Magenta False = "6"
code Cyan    False = "10"
code White   False = "0"
code Black   True  = "14"
code Red     True  = "4"
code Green   True  = "9"
code Yellow  True  = "8"
code Blue    True  = "12"
code Magenta True  = "13"
code Cyan    True  = "11"
code White   True  = "15"
code c@(Rgb _ _ _) b = code (projectToBasicColour8 c) b
