module Parser
  ( listOf'
  , def'
  , prop'
  )
  where

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

import Types


type Parser a = Parsec Void Text a
type Err = ParseErrorBundle Text Void
type Prop' = (Text, Prop, Maybe FilePath)

listOf' :: Parser a -> FilePath -> IO (Either String [a])
listOf' p f
  = prettifyErr . parse (listOf p) f <$> T.readFile f

listOf :: Parser a -> Parser [a]
listOf p = p `endBy1` eol <* skipManyTill space eof

prettifyErr :: Either Err a -> Either String a
prettifyErr = either (Left . errorBundlePretty) Right

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
  pName <- takeWhile1P (Just "name") (/= '\t')
  void tab
  pProp <- lex "`" *> prop <* lex "`" <?> "proposition"
  void tab
  pFile <- takeWhileP (Just "proof file") (Char.isPrint)

  return
    ( pType <> ":" <> pName
    , pProp
    , if T.null pFile then Nothing else Just (T.unpack pFile)
    )

def' :: Parser (Text, Prop)
def' = do
  dName <- takeWhile1P (Just "name") (/= '\t')
  void tab
  dProp <- lex "`" *> prop <* lex "`" <?> "proposition"
  return (dName, dProp)


expr :: Parser Expr
expr = conjunction <?> "expression"
  where
    conjunction
      = sepBy1 disjunction (lex "/\\")
      >>= liftOne (Expr AN)
    disjunction
      = sepBy1 simpleExpr (lex "\\/")
      >>= liftOne (Expr OR)

    liftOne fn = \case
      []  -> fail "impossible!"
      [x] -> pure x
      xs  -> pure $ fn xs

    simpleExpr  = negation <|> brackets <|> functor'

    negation
      = Expr NO . (:[]) <$> (lex "~" *> expr)

    brackets
      = lex "(" *> expr <* lex ")"

    functor' = lex functor >>= \case
      AN -> fail "unexpected AN functor (use /\\ instead)"
      OR -> fail "unexpected OR functor (use \\/ instead)"
      NO -> fail "unexpected NO functor (use ~(...) instead)"
      fn -> some atom >>= \case
        args | length args == arity fn
          -> pure $ Expr fn (map Atom args)
        _ -> fail
          $ "expected " <> show (arity fn)
          <> " arguments for functor " <> show fn

functor :: Parser Fn
functor = do
  fn <- takeP (Just "functor") 2
  case readFn (T.unpack fn) of
    Just x -> pure x
    Nothing -> fail $ "invalid functor: " <>  show fn

atom :: Parser Char
atom = lex $ satisfy Char.isAlpha

exVars :: Parser [Char]
exVars = lex "?" *> some atom <* lex "." <?> "existential"

prop :: Parser Prop
prop = do
  ex1 <- expr
  res <- optional $ (,,)
    <$> (Implication <$ lex "==>"
      <|>  Equivalence <$ lex "<=>")
    <*> (fromMaybe [] <$> optional exVars)
    <*> expr
  pure $ case res of
    -- ex1 is a consequent without context
    Nothing -> Prop Implication [] [] ex1
    -- ex1 is an antecedent and we unfold it to form context
    Just (knd, vars, ex2) -> Prop knd (unfoldAnd ex1) vars ex2
      where
        unfoldAnd = \case
          Expr AN xs -> xs
          x -> [x]

lex :: Parser a -> Parser a
lex p = p <* skipMany (hidden " ")
