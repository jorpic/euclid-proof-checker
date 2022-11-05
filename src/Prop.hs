module Prop where

import Prelude hiding (lex)
import Control.Monad (void)
import Data.Char qualified as Char
import Data.Maybe (fromMaybe)
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.IO qualified as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char

import Expr (Expr)
import Expr qualified as E


data Prop = Prop
  { from :: Expr
  , ex   :: [Char]
  , to   :: Expr
  }
  deriving (Eq, Show)

type Parser a = Parsec Void Text a
type Err = ParseErrorBundle Text Void
type Prop' = (Text, Prop, Maybe FilePath)

parsePropList :: FilePath -> IO (Either String [Prop'])
parsePropList f
  = mapLeft errorBundlePretty  . parse prop'List f
  <$> T.readFile f

mapLeft :: (a -> b) -> Either a x -> Either b x
mapLeft f = either (Left . f) Right

prop'List :: Parser [Prop']
prop'List = prop' `sepBy1` eol <* eof

prop' :: Parser Prop'
prop' = do
  pType <- choice
    [ "cn"
    , "axiom"
    , "postulate"
    , "proposition"
    , "lemma"
    ]
  void tab
  pName <- takeWhile1P (Just "name") Char.isAlphaNum
  void tab
  pProp <- lex "`" *> prop <* lex "`" <?> "proposition"
  void tab
  pFile <- takeWhileP (Just "proof file") Char.isAlphaNum

  return
    ( pType <> ":" <> pName
    , pProp
    , if T.null pFile then Nothing else Just (T.unpack pFile)
    )

expr :: Parser Expr
expr = conjunction <?> "expression"
  where
    conjunction
      = sepBy1 disjunction (lex "/\\")
      >>= liftOne (E.Expr E.AN)
    disjunction
      = sepBy1 simpleExpr (lex "\\/")
      >>= liftOne (E.Expr E.OR)

    liftOne fn = \case
      []  -> fail "impossible!"
      [x] -> pure x
      xs  -> pure $ fn xs

    simpleExpr  = negation <|> brackets <|> functor'

    negation
      = E.Expr E.NO . (:[]) <$> (lex "~" *> expr)

    brackets
      = lex "(" *> expr <* lex ")"

    functor' = lex functor >>= \case
      E.AN -> fail "unexpected AN functor (use /\\ instead)"
      E.OR -> fail "unexpected OR functor (use \\/ instead)"
      E.NO -> fail "unexpected NO functor (use ~(...) instead)"
      fn -> some atom >>= \case
        args | length args == E.arity fn
          -> pure $ E.Expr fn (map E.Atom args)
        _ -> fail
          $ "expected " <> show (E.arity fn)
          <> " arguments for functor " <> show fn

functor :: Parser E.Fn
functor = do
  fn <- takeP (Just "functor") 2
  case E.readFn (T.unpack fn) of
    Just x -> pure x
    Nothing -> fail $ "invalid functor: " <>  show fn

atom :: Parser Char
atom = lex $ satisfy Char.isAlpha

exVars :: Parser [Char]
exVars = lex "?" *> some atom <* lex "." <?> "existential"

prop :: Parser Prop
prop = do
  from <- expr <* lex "==>"
  ex <- fromMaybe [] <$> optional exVars
  to <- expr
  pure $ Prop {..}

lex :: Parser a -> Parser a
lex p = p <* skipMany (hidden " ")
