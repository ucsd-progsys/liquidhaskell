import Test.Build
import Test.Options
import Options.Applicative

main :: IO ()
main = program stackTestEnv stackOutputStripper stackErrorStripper stackBuild =<< execParser opts
