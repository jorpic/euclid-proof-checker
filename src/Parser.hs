module Parser
  ( listOf'
  , def'
  , prop'
  , proofBlock
  , exprCC
  , exprHR
  )
  where

import Prelude hiding (lex)
import Control.Monad (void, forM, when)
import Data.Char qualified as Char
import Data.Maybe (fromMaybe)
import Data.Text qualified as TS
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.IO qualified as T
import Data.Void (Void)
import Text.Megaparsec hiding (Token)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer (decimal)

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
proofBlock = space >> choice
  [ kw "cases" *> proofByCases
  , lex exprCC >>= \ex ->
    choice
      [ kw "assumption" >> ln >> proofByContradiction ex
      , kw "reductio" >> fail "reductio without assumption"
      , Infer ex . TS.strip . TS.pack <$> many printChar
      ]
  ]
  where
    proofByCases = do
      goal <- lex exprCC <* lex ":"
      cases <- lex (exprCC `sepBy1` "|") <* ln
      proofs <- forM (zip [1..] cases) ((<* ln) . oneCaseProof)
      goal' <- lex exprCC <* kw "cases"
      when (goal' /= goal)
        $ fail "case conclusion does not match the goal"
      return $ Cases goal proofs

    oneCaseProof :: (Int, Expr) -> Parser (Expr, Proof)
    oneCaseProof (i, ex) = do
      i' <- kw "case" *> lex decimal <* lex ":"
      when (i' /= i)
        $ fail "case numbers must be consecutive"
      ex' <- lex exprCC <* ln
      when (ex' /= ex)
        $ fail "invalid case expression"
      proof <- (proofBlock <* ln) `someTill` (kw "qedcase")
      return (ex, proof)

    proofByContradiction ex = do
      (proof, conclusion) <-
        (proofBlock <* ln) `manyTill_` (try $ lex exprCC <* kw "reductio")
      return $ Reductio ex conclusion proof



exprCC :: Parser Expr
exprCC = do
  takeP (Just "functor") 2 >>= \case
    "NO" -> NO <$> exprCC
    "AN" -> AN <$> sepBy1 exprCC "+"
    "OR" -> OR <$> sepBy1 exprCC "|"
    fn -> do
      fn' <- readFn fn
      args <- T.unpack <$> takeWhile1P (Just "args") Char.isAlpha
      if length args == arity fn'
         then pure $ Fun fn' args
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
      >>= liftOne AN
    disjunction
      = sepBy1 simpleExpr (lex "\\/")
      >>= liftOne OR

    liftOne fn = \case
      []  -> fail "impossible!"
      [x] -> pure x
      xs  -> pure $ fn xs

    simpleExpr  = negation <|> brackets <|> functor'

    negation
      = NO <$> (lex "~" *> exprHR)

    brackets
      = lex "(" *> exprHR <* lex ")"

    functor' = do
      fn <- lex functor
      some atom >>= \case
        args | length args == arity fn
          -> pure $ Fun fn args
        _ -> fail
          $ "expected " <> show (arity fn)
          <> " arguments for functor " <> show fn

functor :: Parser Fn
functor = takeP (Just "functor") 2 >>= readFn

readFn :: Text -> Parser Fn
readFn fn =
  case reads $ T.unpack fn of
    [(x,"")] -> pure x
    _ -> fail $ "invalid functor: " <>  show fn

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
          AN xs -> xs
          x -> [x]

lex, kw :: Parser a -> Parser a
lex p = p <* skipMany (hidden " ") -- FIXME: hspace?
kw p = lex $ try $ p <* lookAhead (space1 <|> eof)
ln :: Parser ()
ln = eol >> hidden space

linesOf :: Parser a -> Parser [a]
linesOf p = space *> some (p <* (ln <|> lookAhead eof)) <* eof
