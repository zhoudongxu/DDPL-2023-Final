module Main where
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [n] -> putStrLn $ "Hello, " ++ n
    _   -> putStrLn "Usage: hello NAME"
