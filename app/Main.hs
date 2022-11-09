module Main (main) where

import System.Environment (getArgs)
import System.FilePath ((</>))
import Parser qualified

main :: IO ()
main = getArgs >>= \case
  [proofDir] -> main' proofDir
  _ -> putStrLn "help!"

main' :: FilePath -> IO ()
main' proofDir = do
  defs <- Parser.listOf' Parser.def' (proofDir </> "Definitions.txt")
    >>= either fail pure

  props <- Parser.listOf' Parser.prop' (proofDir </> "Theorems.txt")
    >>= either fail pure

  print $ length defs
  print $ length props
