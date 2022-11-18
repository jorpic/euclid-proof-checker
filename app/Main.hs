module Main (main) where

import Control.Exception
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as H
import System.Environment (getArgs)
import System.FilePath ((</>))

import Types
import Parser qualified

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

  evalStateT
    (mapM_ (checkProp proofDir) $ defs ++ props)
    $ ProverState H.empty


data ProverState = ProverState
  { provedFacts :: HashMap PropName Prop
  }

checkProp :: FilePath -> PropWithInfo -> StateT ProverState IO ()
checkProp proofDir (name, prop, proofFile) = do
  facts <- gets provedFacts
  whenJust proofFile $ \file -> do
    liftIO $ print name
    tryX
      $ checkProof facts prop
      <$> tryX (Parser.proof $ proofDir </> file)
  modify (\s -> s {provedFacts = H.insert name prop facts})

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust = flip $ maybe (pure ())

tryX :: MonadIO m => m (Either String b) -> m b
tryX f =  f >>= either (liftIO . throwIO . StringException) pure


checkProof :: HashMap PropName Prop -> Prop -> Proof -> Either String ()
checkProof facts (Prop{..}) proof = proofLoop from proof
  where
    proofLoop _ [] = Right ()
    proofLoop _ _ = Left "proof checker is not implemented"
