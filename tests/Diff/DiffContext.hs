{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Algorithm.DiffContext
-- Copyright   :  (c) David Fox (2015)
-- License     :  BSD 3 Clause
-- Maintainer  :  s.clover@gmail.com
-- Stability   :  experimental
-- Portability :  portable
-- Author      :  David Fox (ddssff at the email service from google)
--
-- Generates a grouped diff with merged runs, and outputs them in the manner of @diff -u@.
-----------------------------------------------------------------------------
module DiffContext
    ( ContextDiff, Hunk
    , getContextDiff
    , prettyContextDiff
    , prettyContextDiffOld
    , getContextDiffNumbered
    , Numbered(Numbered), numbered, unnumber
    , unNumberContextDiff
    ) where

import Diff (PolyDiff(..), Diff, getGroupedDiff,
                            noStuttering, noFFSS,
                            headIsFirst, headIsSecond)
import Data.Bifunctor
import Text.PrettyPrint (Doc, text, empty, hcat)

{-@ type ContextDiff c = [Hunk c] @-}
-- | A diff consisting of disjoint 'Hunk's.
type ContextDiff c = [Hunk c]

{-@ type Hunk c = { h : [ValidListDiff c c] | noStuttering h} @-}
-- | A 'Hunk' is a list of adjacent 'Diff's.
--
-- No two consecutive elements in a 'Hunk' are both applications
-- of 'First', 'Second', or 'Both', i.e. the list does not stutter
-- on 'Diff' constructors.
type Hunk c = [Diff [c]]

-- | Split a 'Diff' list at consecutive 'Both'-'Both' boundaries.
{-@ splitBothBoth :: {ds:[ValidListDiff c c] | noFFSS ds} -> [Hunk c] @-}
splitBothBoth :: [Diff [c]] -> [Hunk c]
splitBothBoth = go []
  where
    {-@ go
          :: g:Hunk c
          -> {xs : [ValidListDiff c c] | noFFSS xs && not (headAlike g xs) }
          -> [Hunk c] / [len xs]
      @-}
    go :: Hunk c -> [Diff [c]] -> [Hunk c]
    go g (x@Both{} : y@Both{} : xs) = reverse (x:g) : go [] (y:xs)
      where
        lemma = lemmaReverseStuttering (x:g)
    go g (x : xs) = go (x:g) xs
    go g [] = [reverse g]
      where
        lemma = lemmaReverseStuttering g

{-@ type ContextSize = Nat @-}
type ContextSize = Int

{-@ opaque-reflect reverse @-}

{-@ assume lemmaReverseStuttering
      :: xs:_ -> { noStuttering (reverse xs) = noStuttering xs } @-}
lemmaReverseStuttering :: Hunk c -> ()
lemmaReverseStuttering _ = ()

{-@ reflect headAlike  @-}
headAlike :: Hunk c -> Hunk c -> Bool
headAlike (Both{} : _) (Both{} : _) = True
headAlike (First{} : _) (First{} : _) = True
headAlike (Second{} : _) (Second{} : _) = True
headAlike _ _ = False

data Numbered a = Numbered Int a deriving Show
instance Eq a => Eq (Numbered a) where
  Numbered _ a == Numbered _ b = a == b
instance Ord a => Ord (Numbered a) where
  compare (Numbered _ a) (Numbered _ b) = compare a b

numbered :: [a] -> [Numbered a]
numbered xs = fmap (uncurry Numbered) (zip [1..] xs)

unnumber :: Numbered a -> a
unnumber (Numbered _ a) = a

-- |
-- > > let textA = ["a","b","c","d","e","f","g","h","i","j","k"]
-- > > let textB = ["a","b","d","e","f","g","h","i","j"]
-- > > let diff = getContextDiff (Just 2) textA textB
-- > > prettyContextDiff (text "file1") (text "file2") (text . unnumber) diff
-- > --- file1
-- > +++ file2
-- > @@ -1,5 +1,4 @@
-- >  a
-- >  b
-- > -c
-- >  d
-- >  e
-- > @@ -9,3 +8,2 @@
-- >  i
-- >  j
-- > -k
{-@
getContextDiff ::
  Eq a
  => Maybe ContextSize
  -> [a]
  -> [a]
  -> ContextDiff (Numbered a)
@-}
getContextDiff ::
  Eq a
  => Maybe ContextSize -- ^ Context size. 'Nothing' means returning a whole-diff 'Hunk'.
  -> [a]
  -> [a]
  -> ContextDiff (Numbered a)
getContextDiff contextSize a b =
  getContextDiffNumbered contextSize (numbered a) (numbered b)

-- | If for some reason you need the line numbers stripped from the
-- result of 'getContextDiff' for backwards compatibility.
{-@ unNumberContextDiff :: ContextDiff (Numbered a) -> [[Diff [a]]] @-}
unNumberContextDiff :: ContextDiff (Numbered a) -> ContextDiff a
unNumberContextDiff = fmap (fmap (bimap (fmap unnumber) (fmap unnumber)))

-- | Create a diff of separate 'Hunk's, each containing a sequence
-- of differing elements surrounded by common elements for context.
--
-- The context size determines when to merge adjacent hunks:
-- two hunks are merged when the number of common elements between them does not
-- exceed twice the context size. Furthermore, if @contextSize@ is 'Nothing'
-- a single hunk with the whole diff is produced.
{-@
getContextDiffNumbered ::
  Eq a
  => Maybe ContextSize
  -> [Numbered a]
  -> [Numbered a]
  -> ContextDiff (Numbered a)
@-}
getContextDiffNumbered ::
  Eq a
  => Maybe ContextSize -- ^ Context size. 'Nothing' means returning a whole-diff 'Hunk'.
  -> [Numbered a]
  -> [Numbered a]
  -> ContextDiff (Numbered a)
getContextDiffNumbered Nothing a0 b0 = [getGroupedDiff a0 b0]
getContextDiffNumbered (Just contextSize) a0 b0 =
    -- The 'Diff' list is grouped into 'Hunks' that begin and end
    -- with matching ('Both') text, having non-matching ('First' and 'Second')
    -- text in the middle. Note that a non-trivial partition can only happen after
    -- the matching text has been reduced to become consecutive 'Both' values
    -- corresponding to a hunk's suffix and the following hunk prefix.
    splitBothBoth $ doPrefix $ getGroupedDiff a0 b0
    where
      -- | Handle the common text leading up to a diff.
      --
      -- Postcondition: The @a@ elements in @doPrefix h@ are a subset of those in @h@,
      -- in the same order. Additionaly, 'First' and 'Second' diffs
      -- are identical in both lists.
      --
      -- The difference between input and output is that some 'Both' diffs might
      -- be split into two other 'Both' diffs. This happens when their contents
      -- are too large compared with the contex size, resulting in some @a@
      -- elements being dropped.
      {-@ doPrefix ::  h : Hunk c
                   -> {v : [ValidListDiff c c] | noFFSS v
                       && (headIsFirst h <=> headIsFirst v)
                       && (headIsSecond h <=> headIsSecond v)} / [len h, 0] @-}
      doPrefix :: [Diff [c]] -> [Diff [c]]
      doPrefix [] = []
      -- Trailing common elements are no prefix.
      -- This case corresponds to when both input lists are identical, so the
      -- resulting 'ContextDiff' is empty.
      doPrefix [Both _ _] = []
      -- Do the prefix and then make the suffix.
      doPrefix (Both xs ys : more) =
        Both (drop (length xs - contextSize) xs)
             (drop (length ys - contextSize) ys) : doSuffix more
      -- Prefix finished, do the diff then the following suffix.
      doPrefix (d : ds) = d : doSuffix ds

      -- | Handle the common text following a diff.
      --
      -- Precondition: The input does not start with a 'Both' diff. Otherwise,
      -- it behaves like @doPrefix@.
      {-@ doSuffix ::  h : Hunk c
                   -> {v : [ValidListDiff c c] | noFFSS v
                       && (headIsFirst h <=> headIsFirst v)
                       && (headIsSecond h <=> headIsSecond v)} / [len h, 1] @-}
      doSuffix :: [Diff [c]] -> [Diff [c]]
      doSuffix [] = []
      -- A trailing suffix.
      doSuffix [Both xs ys] = [Both (take contextSize xs) (take contextSize ys)]
      -- If the common text is too short compared with the context,
      -- we preserve it and continue. As the following element cannot be a 'Both'
      -- as well, this effectively places the common text in the inner part of the diff.
      -- Otherwise, we split it into a suffix and prefix
      -- (resulting in some elements excluded from the diff in the middle).
      doSuffix (Both xs ys : more)
        | length xs <= contextSize * 2 =
            Both xs ys : doPrefix more
        | otherwise =
            Both (take contextSize xs) (take contextSize ys) :
            doPrefix (Both (drop contextSize xs) (drop contextSize ys) : more)
      -- 'First' and 'Second' elements are no suffix, preserve them and continue looking.
      doSuffix (d : ds) = d : doSuffix ds

-- | Pretty print a ContextDiff in the manner of diff -u.
prettyContextDiff ::
       Doc            -- ^ Document 1 name
    -> Doc            -- ^ Document 2 name
    -> (Numbered c -> Doc)     -- ^ Element pretty printer
    -> ContextDiff (Numbered c)
    -> Doc
prettyContextDiff _ _ _ [] = empty
prettyContextDiff old new prettyElem hunks =
    hcat . map (<> text "\n") $ (text "--- " <> old :
                                 text "+++ " <> new :
                                 concatMap prettyRun hunks)
    where
      -- Pretty print a run of adjacent changes
      prettyRun hunk =
        text ("@@ " <> formatHunk hunk <> " @@") : concatMap prettyChange hunk

      -- Pretty print a single change (e.g. one line of a text file)
      prettyChange (Both ts _) = map (\ l -> text " " <> prettyElem l) ts
      prettyChange (First ts)  = map (\ l -> text "-" <> prettyElem l) ts
      prettyChange (Second ts) = map (\ l -> text "+" <> prettyElem l) ts

      formatHunk hunk = "-" <> formatRun (firsts hunk) <> " +" <> formatRun (seconds hunk)

      formatRun :: [Int] -> String
      formatRun [] = "-0,0"
      formatRun [n] = show n
      formatRun ns@(n : _) = show n <> "," <> show (length ns)

      firsts (Both ns _ : more) = fmap (\(Numbered n _) -> n) ns <> firsts more
      firsts (First ns : more) = fmap (\(Numbered n _) -> n) ns <> firsts more
      firsts (Second _ : more) = firsts more
      firsts [] = []

      seconds (Both _ ns : more) = fmap (\(Numbered n _) -> n) ns <> seconds more
      seconds (First _ : more) = seconds more
      seconds (Second ns : more) = fmap (\(Numbered n _) -> n) ns <> seconds more
      seconds [] = []

-- | Pretty print without line numbers.
prettyContextDiffOld ::
       Doc            -- ^ Document 1 name
    -> Doc            -- ^ Document 2 name
    -> (c -> Doc)     -- ^ Element pretty printer
    -> ContextDiff c
    -> Doc
prettyContextDiffOld _ _ _ [] = empty
prettyContextDiffOld old new prettyElem hunks =
    hcat . map (<> text "\n") $ (text "--- " <> old :
                                 text "+++ " <> new :
                                 concatMap prettyRun hunks)
    where
      -- Pretty print a run of adjacent changes
      prettyRun hunk =
          text "@@" : concatMap prettyChange hunk

      -- Pretty print a single change (e.g. one line of a text file)
      prettyChange (Both ts _) = map (\ l -> text " " <> prettyElem l) ts
      prettyChange (First ts)  = map (\ l -> text "-" <> prettyElem l) ts
      prettyChange (Second ts) = map (\ l -> text "+" <> prettyElem l) ts
