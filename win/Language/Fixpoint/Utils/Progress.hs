-- | Progress Bar API
module Language.Fixpoint.Utils.Progress (
      withProgress
    , progressInit
    , progressTick
    , progressClose
    ) where

withProgress :: Int -> IO a -> IO a
withProgress _ x = x

progressInit :: Int -> IO ()
progressInit _ = return ()

progressTick :: IO ()
progressTick = return ()

progressClose :: IO ()
progressClose = return ()
