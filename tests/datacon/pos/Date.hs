{-# LANGUAGE ScopedTypeVariables #-}

-- via https://github.com/chrisdone/sandbox/blob/master/liquid-haskell-dates.hs
-- | Modelling a calendar date statically.

module Date where

-- We define invariants on dates, such as how many days per month, including leap years.

{-@ inline okDay @-}
okDay :: Int -> Bool
okDay v = v > 0 && v <= 31

{-@ inline okMonth @-}
okMonth :: Int -> Int -> Bool
okMonth day v = v > 0 && v <= 12 && (day < 31 || not (v == 04 || v == 06 || v == 09 || v == 11))  

{-@ inline okYear @-}
okYear :: Int -> Int -> Int -> Bool
okYear month day v = v > 0 && (month /= 2 || (day < 30 && (day < 29 ||  (v `mod` 400) == 0 || ( (v `mod` 4) == 0 && (v `mod` 100) /= 0))))

-- We define a date type with a shadow liquid type encoding our invariants.

data Date = Date
  { day   :: !Int
  , month :: !Int
  , year  :: !Int
  } deriving (Show)

{-@ data Date = Date
      { day   :: {v:_ | okDay v }
      , month :: {v:_ | okMonth day v}
      , year  :: {v:_ | okYear month day v}
      }
 @-}

-- In order to construct a valid `Date`, we need to do all the proper runtime tests, or
-- else Liquid Haskell complains at compile time that they're not satisfied.

main :: IO ()
main = do
  year  :: Int <- readLn
  month :: Int <- readLn
  day   :: Int <- readLn
  if year > 0
     then if okMonth day month
         then if okDay day && okYear month day year
                   then print (Date day month year)
                   else error "Day is out of range!"
            else error "Month is out of range."
     else error "Year is out of range."

{-@ assume error :: _ -> _ @-} -- don't report warnings on `error`

-- Examples:

works :: Date
works = Date 12 03 2017

works2 :: Date
works2 = Date 31 03 2017

works3 :: Date
works3 = Date 30 04 2017

works_leap_day :: Date
works_leap_day = Date 29 02 2016

-- Does not compile:
-- invalid_nov_day = Date 11 31 2017
-- invalid_month = Date 12 15 2017
-- invalid_leap_day = Date 29 02 2017
-- invalid_days d m y = Date 30 2 2000
-- invalid_bound = Date 31 04 2017
