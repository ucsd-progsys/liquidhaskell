module Language.Haskell.HsColour.ColourHighlight
  ( Colour(..)
  , Highlight(..)
  , base256, unbase
  , rgb24bit_to_xterm256
  ,   projectToBasicColour8
  , hlProjectToBasicColour8
  ) where

{-@ LIQUID "--totality" @-}

import Data.Word

-- | Colours supported by ANSI codes.
data Colour = Black | Red | Green | Yellow | Blue | Magenta | Cyan | White | Rgb Word8 Word8 Word8
  deriving (Eq,Show,Read)

{-@ measure isBasic :: Colour -> Int
    isBasic (Black)     = 1
    isBasic (Red)       = 1
    isBasic (Green)     = 1
    isBasic (Yellow)    = 1
    isBasic (Blue)      = 1
    isBasic (Magenta)   = 1
    isBasic (Cyan)      = 1
    isBasic (White)     = 1
    isBasic (Rgb r g b) = 0
  @-}

{-@ invariant {v:Colour | (((isBasic v) == 1) || ((isBasic v) == 0))} @-}

{-@ ensureBasic :: String -> Colour -> BasicColour @-}
ensureBasic :: String -> Colour -> Colour
ensureBasic msg (Rgb _ _ _) = error $ "ensureBasic: " ++ msg 
ensureBasic _   x           = x

{-@ type BasicColour = {v:Colour | (isBasic v) = 1} @-}

-- | Convert an integer in the range [0,2^24-1] to its base 256-triplet, passing the result to the given continuation (avoid unnecessary tupleism).
base256 :: Integral int => (Word8 -> Word8 -> Word8 -> r) -> int -> r
base256 kont x =
    let
        (r,gb) = divMod x 256
        (g,b)  = divMod gb 256
        fi = fromIntegral
    in 
        kont (fi r) (fi g) (fi b)

-- | Convert a three-digit numeral in the given (as arg 1) base to its integer value.
unbase :: Integral int => int -> Word8 -> Word8 -> Word8 -> int
unbase base r g b = (fi r*base+fi g)*base+fi b
    where fi = fromIntegral

-- | Approximate a 24-bit Rgb colour with a colour in the xterm256 6x6x6 colour cube, returning its index.
rgb24bit_to_xterm256 :: (Integral t) => Word8 -> Word8 -> Word8 -> t
rgb24bit_to_xterm256 r g b = let f = (`div` 43)
                          in 16 + unbase 6 (f r) (f g) (f b)


-- | Ap\"proxi\"mate a 24-bit Rgb colour with an ANSI8 colour. Will leave other colours unchanged and will never return an 'Rgb' constructor value. 
{-@ projectToBasicColour8 ::  Colour -> BasicColour @-}
projectToBasicColour8 ::  Colour -> Colour
projectToBasicColour8 (Rgb r g b) = let f = (`div` 128)
                          in  ensureBasic "projectToBasicColour8" $ 
                                toEnum ( unbase 2 (f r) (f g) (f b) )
projectToBasicColour8 x = x


-- | Lift 'projectToBasicColour8' to 'Highlight's
hlProjectToBasicColour8 ::  Highlight -> Highlight
hlProjectToBasicColour8 (Foreground c) = Foreground (projectToBasicColour8 c)
hlProjectToBasicColour8 (Background c) = Background (projectToBasicColour8 c)
hlProjectToBasicColour8 h = h

        

instance Enum Colour where
    toEnum 0 = Black
    toEnum 1 = Red 
    toEnum 2 = Green 
    toEnum 3 = Yellow 
    toEnum 4 = Blue 
    toEnum 5 = Magenta 
    toEnum 6 = Cyan 
    toEnum 7 = White 
    -- Arbitrary extension; maybe just 'error' out instead
    toEnum x = base256 Rgb (x-8)
    
    fromEnum Black   = 0
    fromEnum Red     = 1
    fromEnum Green   = 2
    fromEnum Yellow  = 3
    fromEnum Blue    = 4
    fromEnum Magenta = 5
    fromEnum Cyan    = 6
    fromEnum White   = 7
    -- Arbitrary extension; maybe just 'error' out instead
    fromEnum (Rgb r g b) = 8 + unbase 256 r g b
 

-- | Types of highlighting supported by ANSI codes (and some extra styles).
data Highlight =
    Normal
  | Bold
  | Dim
  | Underscore
  | Blink
  | ReverseVideo
  | Concealed
  | Foreground Colour
  | Background Colour
  -- The above styles are ANSI-supported, with the exception of the 'Rgb' constructor for 'Colour's.  Below are extra styles (e.g. for Html rendering).
  | Italic
  deriving (Eq,Show,Read)




