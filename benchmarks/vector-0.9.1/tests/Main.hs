module Main (main) where

import qualified Tests.Vector
import qualified Tests.Stream
import qualified Tests.Move

import Test.Framework (defaultMain)

main = defaultMain $ Tests.Stream.tests
                  ++ Tests.Vector.tests
                  ++ Tests.Move.tests

