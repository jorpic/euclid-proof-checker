module Parser
  ( listOf'
  , def'
  , prop'
  , proofBlock
  )
  where

import Prelude hiding (lex)
import Control.Monad (void, forM)
import Data.Char qualified as Char
import Data.Maybe (fromMaybe)
import Data.Text qualified as TS
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.IO qualified as T
import Data.Void (Void)
import Text.Megaparsec hiding (Token)
import Text.Megaparsec.Char

import Types


type Parser a = Parsec Void Text a
type Err = ParseErrorBundle Text Void
type Prop' = (Text, Prop, Maybe FilePath)


listOf' :: Parser a -> FilePath -> IO (Either String [a])
listOf' p f
  = prettifyErr . parse (many $ p <* space) f <$> T.readFile f

prettifyErr :: Either Err a -> Either String a
prettifyErr = either (Left . errorBundlePretty) Right

-- FIXME: expalin that we have two syntaxes for expressions
--  - concise one like this: ANEABAFFAC+IABACF
--  - and human readable like this: ~(LT C D A B) /\ NE A B /\ NE C D

proofBlock :: Parser ProofBlock
proofBlock = skipMany " " >> (cases <|> other)
  where
    oneCase :: Parser (Expr, Proof)
    oneCase = do
      void $ lex "case" >> lex (some digitChar) >> lex ":"
      cs <- lex exprCC <* eol
      proof <- proofBlock `manyTill` (skipMany " " >> "qedcase")
      return (cs, proof)

    cases = do
      goal <- lex "cases" *> exprCC <* lex ":"
      caseExprs <- lex $ exprCC `sepBy1` "|"
      eol >> space
      cases' <- forM caseExprs $ \ex -> skipMany " " >> oneCase >>= \case
        cs@(ex', _proof) | ex' == ex -> pure cs
        _ -> fail "case does not match the one declared in head"
      (lex exprCC <* "cases")  >>= \case
        ex' | ex' == goal -> pure $ Cases goal cases'
        _ -> fail "case result does not match declared case goal"

    other = Exact
      <$> lex exprCC
      <*> (TS.strip . TS.pack <$> manyTill asciiChar (void eol <|> eof))

exprCC :: Parser Expr
exprCC = do
  fn <- functor
  Expr fn <$> case fn of
    NO -> (:[]) <$> exprCC
    AN -> sepBy1 exprCC "+"
    OR -> sepBy1 exprCC "|"
    _ -> do
      args <- T.unpack <$> takeWhile1P (Just "args") Char.isAlpha
      if length args == arity fn
         then pure $ map Atom args
         else fail "number of arguments does not match functor arity"

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


exprHR :: Parser Expr
exprHR = conjunction <?> "expression"
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
      = Expr NO . (:[]) <$> (lex "~" *> exprHR)

    brackets
      = lex "(" *> exprHR <* lex ")"

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
  ex1 <- exprHR
  res <- optional $ (,,)
    <$> (Implication <$ lex "==>"
      <|>  Equivalence <$ lex "<=>")
    <*> (fromMaybe [] <$> optional exVars)
    <*> exprHR
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
