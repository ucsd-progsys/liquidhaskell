module spec Data.Time.Calendar where

type NumericMonth = { x:Nat | 0 < x && x <= 12 }

type NumericDayOfMonth = { x:Nat | 0 < x && x <= 31 }

fromGregorian :: Integer -> NumericMonth -> NumericDayOfMonth -> Day

toGregorian :: Day -> (Integer,NumericMonth,NumericDayOfMonth)

gregorianMonthLength :: Integer -> NumericMonth -> { x:Nat | 28 <= x && x <= 31 }
