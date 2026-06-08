{-@ LIQUID "--ple" @-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Algorithm.DiffOutput
-- Copyright   :  (c) Sterling Clover 2008-2011, Kevin Charter 2011
-- License     :  BSD 3 Clause
-- Maintainer  :  s.clover@gmail.com
-- Stability   :  experimental
-- Portability :  portable
-- Author      :  Stephan Wehr (wehr@factisresearch.com) and JP Moresmau (jp@moresmau.fr)
--
-- Generates a string output that is similar to diff normal mode.
-----------------------------------------------------------------------------
module DiffOutput where
import Diff
import Text.PrettyPrint hiding ((<>))
import Data.Char
import Data.List

-- Non-empty lists as refinements of regular lists.
{-@ type NonEmpty a = {xs : [a] | len xs >0}@-}

{-@ reflect coherentDiff @-}
-- | This functions checks that both contents match whenever we have a 'Both'
-- value.
coherentDiff :: Eq c => Diff c -> Bool
coherentDiff (Both x y) = x == y
coherentDiff (First _) = True
coherentDiff (Second _) = True

-- This refinement type synonym encodes the invariants on the 'Diff' type
-- that we expect throughout this module. Namely:
--
-- * They have non-empty contents
-- * 'Both' values have equal arguments
{-@ type StringDiff = {d : Diff (NonEmpty String) | coherentDiff d } @-}

-- | Converts 'Diff's to 'DiffOperation's. 'First' and 'Second'
-- ocurrances are converted to 'Addition' and 'Deletion', respectively, while
-- consecutive ocurrances of them are replaced by a 'Change'.
{-@ diffToLineRanges :: [StringDiff] -> [DiffOperation LineRange]@-}
diffToLineRanges :: [Diff [String]] -> [DiffOperation LineRange]
diffToLineRanges = toLineRange 1 1
   where
          -- | In @toLineRange x y ds@, @x@ is the index of the current string in the
          -- left input of the diff @ds@, and @y@ is the index of the corresponding
          -- string in the right input of the diff @ds@.
          {-@ toLineRange :: {l:Int | l >= 1}
                          -> {r:Int | r >= 1}
                          -> diffs : [StringDiff]
                          -> [DiffOperation LineRange] / [len diffs, 0] @-}
          toLineRange :: Int -> Int -> [Diff [String]] -> [DiffOperation LineRange]
          toLineRange _ _ [] = []
          -- If the lines are the same, we just move forward.
          toLineRange leftLine rightLine (Both ls _ : rs) =
                let lins=length ls
                in  toLineRange (leftLine+lins) (rightLine+lins) rs
          -- A 'Change' is introduced when an addition is followed by a deletion, or vice versa.
          toLineRange leftLine rightLine (Second lsS@(_:_) : First lsF@(_:_) : rs) =
                toChange leftLine rightLine lsF lsS rs
          toLineRange leftLine rightLine (First lsF@(_:_) : Second lsS@(_:_) : rs) =
                toChange leftLine rightLine lsF lsS rs
          -- Introduce 'Addition's.
          toLineRange leftLine rightLine (Second lsS@(_:_) : rs) =
                let diff = Addition (mkLineRange rightLine lsS) (leftLine-1)
                in  diff : toLineRange leftLine (rightLine + length lsS) rs
          -- Introduce 'Deletion's.
          toLineRange leftLine rightLine (First lsF@(_:_):rs)=
                let diff = Deletion (mkLineRange leftLine lsF) (rightLine-1)
                in  diff : toLineRange (leftLine + length lsF) rightLine rs
          -- Skip empty 'Second' and 'First' entries.
          -- NOTE: Both these cases are unreachable.
          toLineRange leftLine rightLine (Second [] : rs) =
                toLineRange leftLine rightLine rs
          toLineRange leftLine rightLine (First [] : rs) =
                toLineRange leftLine rightLine rs
          -- | Build 'Change's from adjacent additions and deletions.
          {-@ toChange :: {l:Int | l >= 1}
                       -> {r:Int | r >= 1}
                       -> {lf:[String] | len lf > 0}
                       -> {ls:[String] | len ls > 0}
                       -> diffs : [StringDiff]
                       -> [DiffOperation LineRange] / [len diffs, 1] @-}
          toChange :: Int -- ^ Current left line number.
                   -> Int -- ^ Current right line number.
                   -> [String] -- ^ Lines from the 'First' list (corresponding to deletions).
                   -> [String] -- ^ Lines from the 'Second' list (corresponding to additions).
                   -> [Diff [String]] -- ^ Remaining 'Diff's.
                   -> [DiffOperation LineRange]
          toChange leftLine rightLine lsF lsS rs=
                Change (mkLineRange leftLine lsF) (mkLineRange rightLine lsS)
                    : toLineRange (leftLine + length lsF) (rightLine + length lsS) rs

{-@ ppDiff :: [StringDiff] -> String @-}
-- | Pretty print the differences. The output is similar to the output of the @diff@ utility.
--
-- > > putStr (ppDiff (getGroupedDiff ["a","b","c","d","e"] ["a","c","d","f"]))
-- > 2d1
-- > < b
-- > 5c4
-- > < e
-- > ---
-- > > f
ppDiff :: [Diff [String]] -> String
ppDiff gdiff =
   let  diffLineRanges = diffToLineRanges gdiff
   in
        render (prettyDiffs diffLineRanges) ++ "\n"


-- | Pretty print of diff operations.
prettyDiffs :: [DiffOperation LineRange] -> Doc
prettyDiffs [] = empty
prettyDiffs (d : rest) = prettyDiff d $$ prettyDiffs rest
    where
      prettyDiff (Deletion inLeft lineNoRight) =
          prettyRange (lrNumbers inLeft) <> char 'd' <> int lineNoRight $$
          prettyLines '<' (lrContents inLeft)
      prettyDiff (Addition inRight lineNoLeft) =
          int lineNoLeft <> char 'a' <> prettyRange (lrNumbers inRight) $$
          prettyLines '>' (lrContents inRight)
      prettyDiff (Change inLeft inRight) =
          prettyRange (lrNumbers inLeft) <> char 'c' <> prettyRange (lrNumbers inRight) $$
          prettyLines '<' (lrContents inLeft) $$
          text "---" $$
          prettyLines '>' (lrContents inRight)
      prettyRange (start, end) =
          if start == end then int start else int start <> comma <> int end
      prettyLines start lins =
          vcat (map (\l -> char start <+> text l) lins)

-- | Parse pretty printed 'Diff's as 'DiffOperation's.
parsePrettyDiffs :: String -> [DiffOperation LineRange]
parsePrettyDiffs = reverse . doParse [] . lines
  where
    -- | Parsing entry point that iteratively accumulates 'DiffOperation's
    -- until the input is exhausted.
    {-@ doParse :: [DiffOperation LineRange] -> diffs : [String] -> [DiffOperation LineRange] / [len diffs] @-}
    doParse :: [DiffOperation LineRange] -> [String] -> [DiffOperation LineRange]
    -- NOTE: Incorrectly formatted lines are ignored.
    doParse acc [] = acc
    doParse acc s =
        let (mnd,r) = parseDiff s
        in case mnd of
            Just nd -> doParse (nd:acc) r
            _          -> doParse acc r

    {-@ parseDiff :: s:{[String] | len s > 0} -> {v:(Maybe (DiffOperation LineRange), [String]) | len (snd v) < len s} @-}
    parseDiff :: [String] -> (Maybe (DiffOperation LineRange), [String])
    parseDiff [] = (Nothing,[])
    parseDiff (h:rs) = let
        (r1,hrs1) = parseRange h
        in case hrs1 of
                -- In each case, we pass the left line range,
                -- the remaining string after the type character,
                -- which must contain the right line range,
                -- and the remaining lines to parse.
                ('d':hrs2) -> parseDel r1 hrs2 rs
                ('a':hrs2) -> parseAdd r1 hrs2 rs
                ('c':hrs2) -> parseChange r1 hrs2 rs
                _ -> (Nothing,rs)

    {-@ parseDel :: (Nat, Nat) -> String -> rs:[String] -> {v:(Maybe (DiffOperation LineRange), [String]) | len (snd v) <= len rs} @-}
    parseDel :: (LineNo, LineNo) -> String -> [String] -> (Maybe (DiffOperation LineRange), [String])
    parseDel r1 hrs2 rs = let
        (r2,_) = parseRange hrs2
        (ls,rs2) = span (isPrefixOf "<") rs
        contents = map (drop 2) ls
        in case contents of
            (_:_) -> (Just $ Deletion (mkLineRange (fst r1) contents) (fst r2), rs2)
            _ -> (Nothing, rs2)

    {-@ parseAdd :: (Nat, Nat) -> String -> rs:[String] -> {v:(Maybe (DiffOperation LineRange), [String]) | len (snd v) <= len rs} @-}
    parseAdd :: (LineNo, LineNo) -> String -> [String] -> (Maybe (DiffOperation LineRange), [String])
    parseAdd r1 hrs2 rs = let
        (r2,_) = parseRange hrs2
        (ls,rs2) = span (isPrefixOf ">") rs
        contents = map (drop 2) ls
        in case contents of
            (_:_) -> (Just $ Addition (mkLineRange (fst r2) contents) (fst r1), rs2)
            _ -> (Nothing, rs2)

    {-@ parseChange :: (Nat, Nat) -> String -> rs:[String] -> {v:(Maybe (DiffOperation LineRange), [String]) | len (snd v) <= len rs} @-}
    parseChange :: (LineNo, LineNo) -> String -> [String] -> (Maybe (DiffOperation LineRange), [String])
    parseChange r1 hrs2 rs = let
        (r2,_) = parseRange hrs2
        (ls1,rs2) = span (isPrefixOf "<") rs
        in case rs2 of
            -- The left and right diff of a 'Change' are separated by a "---" line.
            ("---":rs3) -> let
                (ls2,rs4) = span (isPrefixOf ">") rs3
                contents1 = map (drop 2) ls1
                contents2 = map (drop 2) ls2
                in case (contents1, contents2) of
                    (_:_, _:_) -> (Just $ Change (mkLineRange (fst r1) contents1) (mkLineRange (fst r2) contents2), rs4)
                    _ -> (Nothing, rs4)
            _ -> (Nothing,rs2)

    {-@ parseRange :: String -> {v : ((Nat, Nat), String) | fst (fst v) <= snd (fst v)} @-}
    parseRange :: String -> ((LineNo, LineNo), String)
    parseRange l = let
        (fstLine,rs) = span isDigit l
        a = max 0 (read fstLine)
        (sndLine,rs3) = case rs of
                                    -- The comma is used to separate
                                    -- the start and end line numbers in a range,
                                    -- but is omitted if they are the same.
                                    -- i.e. the range is a single line.
                                    (',':rs2) -> span isDigit rs2
                                    _ -> (fstLine,rs)
        b = max a (read sndLine)
        in ((a, b), rs3)

-- | Line number alias. Always non-negative.
type LineNo = Int

-- | Line Range: start, end and contents.
--
-- The following invariants hold:
--
-- > snd lrNumbers >= fst lrNumbers
-- > snd lrNumbers - fst lrNumbers + 1 == length lrContents
--
-- which imply @lrContents@ cannot be empty.
{-@
data LineRange = LineRange { lrNumbers :: {range : (Nat, Nat) | fst range <= snd range}
                           , lrContents :: {contents : [String] | snd lrNumbers - fst lrNumbers = len contents - 1}
                           }
@-}
data LineRange = LineRange { lrNumbers :: (LineNo, LineNo)
                           , lrContents :: [String]
                           }
            deriving (Show, Read, Eq, Ord)

-- | Smart constructor for 'LineRange' that computes the end line from the
-- start line and the content length, guaranteeing that its content length and
-- range match.
{-@ mkLineRange :: start:Nat -> contents:{[String] | len contents > 0} -> LineRange @-}
mkLineRange :: Int -> [String] -> LineRange
mkLineRange start contents = LineRange (start, start + length contents - 1) contents

-- | Diff operation representing changes to apply.
data DiffOperation a
  = Deletion a LineNo  -- ^ Element deleted on the left input, line number
                       -- preceding the deleted lines in the right input.
  | Addition a LineNo  -- ^ Element added from the right input, line number
                       -- preceding the added lines in the left input.
  | Change a a         -- ^ Element changed from the left input to the right input.
  deriving (Show,Read,Eq,Ord)
