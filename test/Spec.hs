{-# LANGUAGE DeriveGeneric #-}

import Test.Hspec
import ParserSpec qualified

main :: IO ()
main = do
  hspec ParserSpec.spec
