-- See https://github.com/ucsd-progsys/liquidhaskell/issues/1137

import Data.List

{-@ type WeekDayNum = { i:Int | 0 < i && i <= 7 } @-}
type WeekDayNum = Int -- Mon == 1, ..., Sun == 7

data WeekDay = Mon | Tue | Wed | Thu | Fri | Sat | Sun
  deriving (Read, Show, Eq, Bounded)

{-@ weekdays :: { wd:[WeekDay] | len wd == 7 } @-}
weekdays :: [WeekDay]
weekdays = [Mon, Tue, Wed, Thu, Fri, Sat, Sun]

{-@ fromWeekDayNum :: WeekDayNum -> WeekDay @-}
fromWeekDayNum :: WeekDayNum -> WeekDay
fromWeekDayNum i = weekdays !! (i-1)

{-@ fromWeekDayNum :: WeekDay -> WeekDayNum @-}
toWeekDayNum :: WeekDay -> WeekDayNum
toWeekDayNum wd = case wd `elemIndex` weekdays of
		    Just i -> i + 1
