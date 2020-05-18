import Language.Haskell.Liquid.Liquid (liquid)
import System.Environment             (getArgs)
-- import GhcTest 

main :: IO a
main = liquid =<< getArgs
