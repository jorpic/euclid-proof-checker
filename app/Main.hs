module Main (main) where

import Control.Monad (forM_)
import System.Environment (getArgs)
import System.FilePath ((</>))
import Parser qualified

main :: IO ()
main = getArgs >>= \case
  [proofDir] -> main' proofDir
  _ -> putStrLn "help!"

main' :: FilePath -> IO ()
main' proofDir = do
  defs <- Parser.listOf' Parser.prop' (proofDir </> "Definitions.txt")
    >>= either fail pure

  props <- Parser.listOf' Parser.prop' (proofDir </> "Theorems.txt")
    >>= either fail pure

  print $ length defs
  print $ length props

  forM_ defs print
  forM_ props print

  forM_ props $ \case
    (name, prop, Just file) -> do
      print (name, file)
      print prop
      proof <- Parser.listOf' Parser.proofBlock (proofDir </> file)
        >>= either fail pure
      mapM_ print proof

    _ -> return ()
