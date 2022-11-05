module Main (main) where

import System.Environment (getArgs)
import Prop qualified

main :: IO ()
main = getArgs >>= \case
  [path] -> Prop.parsePropList path >>= \case
    Left err -> putStrLn err
    Right res -> print $ length res
  _ -> putStrLn "hello!"
