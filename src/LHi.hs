import System.Environment             (getArgs)

main :: IO a
main = liquid =<< getArgs

lhi _ = putStrLn "Hello!"
