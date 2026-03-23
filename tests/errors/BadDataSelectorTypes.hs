{-@ LIQUID "--expect-error-containing=(A) ox :: GHC.Internal.Types.Int" @-}
{-@ LIQUID "--expect-error-containing=(B) ox :: GHC.Internal.Types.Bool" @-}

module BadDataSelectorTypes where

{-@ data Clash
      = A { ox :: Int  }
      | B { ox :: Bool }
  @-}
data Clash
  = A Int
  | B Bool

main :: IO ()
main = pure ()
