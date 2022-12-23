module Main (main) where

import Control.Exception
import Control.Monad (foldM_)
import Control.Monad.IO.Class
import Data.Map.Strict qualified as Map
import System.Environment (getArgs)
import System.FilePath ((</>))

import Parser qualified
import ProofChecker (checkProof)


data AnyErr = StringException String
  deriving Show

instance Exception AnyErr

main :: IO ()
main = getArgs >>= \case
  [proofDir] -> main' proofDir
    `catch` (\(StringException e) -> putStrLn e)
  _ -> putStrLn "help!"


main' :: FilePath -> IO ()
main' proofDir = do
  defs <- tryX $ Parser.props $ proofDir </> "Definitions.txt"
  props <- tryX $ Parser.props $ proofDir </> "Theorems.txt"

  let foldProps f = foldM_ f Map.empty $ defs ++ props
  foldProps $ \facts (name, prop, proofFile) -> do
    whenJust proofFile $ \file -> do
      liftIO $ print name
      proof <- tryX $ Parser.proof $ proofDir </> file
      tryX $ pure $ checkProof facts prop proof
    pure $ Map.insert name prop facts

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust = flip $ maybe (pure ())

-- | convert Left into throwIO
tryX :: MonadIO m => m (Either String b) -> m b
tryX f =  f >>= either (liftIO . throwIO . StringException) pure
