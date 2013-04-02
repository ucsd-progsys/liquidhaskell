module Data.Text.Axioms where

import qualified Data.Text.Array as A
import Data.Text.Internal


axiom_numchars_append :: Text -> Text -> Text -> Bool
axiom_numchars_append a b t = True

axiom_numchars_replicate :: Text -> Text -> Bool
axiom_numchars_replicate t t' = True

axiom_numchars_split :: Text -> Int -> Bool
axiom_numchars_split t i = True


nc :: A.Array -> Int -> Int -> Int
nc a o l = l

tl :: Text -> Int
tl (Text a o l) = l
