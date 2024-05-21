import Test.Build
import Test.Options

main :: IO ()
main = program stackTestEnv stackRun =<< parseOptions
