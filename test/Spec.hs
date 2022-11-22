{-# LANGUAGE DeriveGeneric #-}

import Test.Hspec
import ParserSpec qualified
import ProofCheckerSpec qualified

main :: IO ()
main = do
  hspec ParserSpec.spec
  hspec ProofCheckerSpec.spec
