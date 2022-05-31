{-@ LIQUID "--expect-any-error" @-}
module Multi_pred_app_00 () where

{-@ bar :: forall < p :: Int -> Bool, q :: Int -> Bool>. Int<p> -> Int<p, q> @-}
bar :: Int -> Int
bar x = x
