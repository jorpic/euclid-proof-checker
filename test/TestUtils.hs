{-# OPTIONS_GHC -fno-warn-orphans #-}
module TestUtils where

import Data.String
import Data.Text.Lazy qualified as T
import Text.Megaparsec (parse)

import Types (Expr)
import Parser (exprCC)

instance IsString Expr where
  fromString
    = either (error . show) id
    . parse exprCC "" . T.pack
