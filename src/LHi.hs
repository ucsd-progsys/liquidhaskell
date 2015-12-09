import System.Environment             (getArgs)

main :: IO ()
main = lhi =<< getArgs

lhi _ = putStrLn "Hello, world!"
