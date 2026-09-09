{-# LANGUAGE UnicodeSyntax #-}

module UnicodeConstraints where

{-@ id10 :: (Ord a) => a -> a @-}
id10 :: Ord a => a -> a
id10 x = x

{-@ id11 :: (Ord a) => a -> a @-}
id11 ∷ Ord a ⇒ a → a
id11 x = x

{-@ id20 ∷ (Ord a) ⇒ a → a @-}
id20 :: Ord a => a -> a
id20 x = x

{-@ id21 ∷ (Ord a) ⇒ a → a @-}
id21 ∷ Ord a ⇒ a → a
id21 x = x
