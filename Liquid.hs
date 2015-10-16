import Language.Haskell.Liquid.Liquid (liquid)
import System.Environment             (getArgs)

main :: IO a
main = liquid =<< getArgs
