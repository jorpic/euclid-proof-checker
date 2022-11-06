module Main (main) where

import System.Environment (getArgs)
import System.FilePath ((</>))
import Prop qualified

main :: IO ()
main = getArgs >>= \case
  [proofDir] -> main' proofDir
  _ -> putStrLn "help!"

main' :: FilePath -> IO ()
main' proofDir = do
  defs <- Prop.parseListOf Prop.def' (proofDir </> "Definitions.txt")
    >>= either fail pure

  props <- Prop.parseListOf Prop.prop' (proofDir </> "Theorems.txt")
    >>= either fail pure

  print $ length defs
  print $ length props
