module Parser
  ( proof
  , props
  , proofBlock
  , propWithInfo
  , exprCC
  , exprHR
  )
  where

import Prelude hiding (lex)
import Control.Exception (Exception)
import Control.Monad (void, forM, when)
import Control.Monad.IO.Class
import Data.Maybe (fromMaybe)
import Data.Text qualified as TS
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.IO qualified as T
import Data.Void (Void)
import Text.Megaparsec hiding (Token)
import Text.Megaparsec.Char

import Types
import Utils (mapLeft)

type Parser a = Parsec Void Text a
type Err = ParseErrorBundle Text Void

newtype ParserErr = ParserErr Err
  deriving Exception

instance Show ParserErr where
  show (ParserErr e) = errorBundlePretty e

proof :: MonadIO m => FilePath -> m (Either ParserErr Proof)
proof = parseFile $ linesOf proofBlock

props :: MonadIO m => FilePath -> m (Either ParserErr [PropWithInfo])
props = parseFile $ linesOf propWithInfo

parseFile :: MonadIO m => Parser a -> FilePath -> m (Either ParserErr a)
parseFile p f = mapLeft ParserErr . parse p f <$> liftIO (T.readFile f)

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
      proofs <- forM cases ((<* ln) . oneCaseProof)
      goal' <- lex exprCC <* kw "cases"
      when (goal' /= goal)
        $ fail "case conclusion does not match the goal"
      return $ Cases goal proofs

    oneCaseProof :: Expr -> Parser (Expr, Proof)
    oneCaseProof ex = do
      -- NB. case number checking was deliberatly disabled
      kw "case" >> skipManyTill anySingle ":" >> hspace
      ex' <- lex exprCC <* ln
      when (ex' /= ex)
        $ fail "invalid case expression"
      proof <- (proofBlock <* ln) `manyTill` (kw "qedcase")
      return (ex, proof)

    proofByContradiction ex = do
      (proof, conclusion) <-
        (proofBlock <* ln) `manyTill_` (try $ lex exprCC <* kw "reductio")
      return $ Reductio ex conclusion proof

-- FIXME: expalin that we have two syntaxes for expressions
--  - concise one like this: ANEABAFFAC+IABACF
--  - and human readable like this: ~(LT C D A B) /\ NE A B /\ NE C D

exprCC :: Parser Expr
exprCC = do
  count 2 letterChar >>= \case
    "NO" -> NO <$> exprCC
    "AN" -> AN <$> sepBy1 exprCC "+"
    "OR" -> OR <$> sepBy1 exprCC "|"
    fn -> readFnArgs letterChar fn

exprHR :: Parser Expr
exprHR = conjunction <?> "expression"
  where
    conjunction = sepBy1 disjunction (lex "/\\") >>= liftOne AN
    disjunction = sepBy1 simpleExpr (lex "\\/") >>= liftOne OR
    simpleExpr  = negation <|> brackets <|> functor
    negation = NO <$> (lex "~" *> exprHR)
    brackets = lex "(" *> exprHR <* lex ")"
    functor = lex (count 2 letterChar) >>= readFnArgs (lex letterChar)

    liftOne fn = \case
      []  -> fail "impossible!"
      [x] -> pure x
      xs  -> pure $ fn xs

readFnArgs :: Parser Char -> String -> Parser Expr
readFnArgs p s = case reads s of
  [(fn,"")] -> some p >>= \case
    args | length args == arity fn
      -> pure $ Fun fn args
    _ -> fail
      $ "expected " <> show (arity fn)
      <> " arguments for functor " <> show fn
  _ -> fail $ "invalid functor: " <>  show s

propWithInfo :: Parser PropWithInfo
propWithInfo = do
  pType <- choice
    [ "cn"          <* tab
    , "axiom"       <* tab
    , "postulate"   <* tab
    , "proposition" <* tab
    , "lemma"       <* tab
    , pure "defn"
    ]
  pName <- takeWhile1P (Just "name") (/= '\t')
  void tab
  pProp <- lex "`" *> prop <* lex "`" <?> "proposition"
  hspace
  pFile <- optional $ some printChar <* hspace

  return
    ( T.toStrict $ pType <> ":" <> pName
    , pProp
    , pFile
    )

exVars :: Parser [Char]
exVars = lex "?" *> some (lex letterChar) <* lex "." <?> "existential"

prop :: Parser Prop
prop = exprHR >>= \ex1 ->
  choice
    [ -- ex1 is an antecedent and we unfold it to form context
      (lex $ "==>" <|>  "<=>")
      >> Prop (unfoldAnd ex1)
        <$> (fromMaybe [] <$> optional exVars)
        <*> exprHR
      -- ex1 is a consequent without context
    , pure $ Prop [] [] ex1
    ]
  where
    unfoldAnd = \case
      AN xs -> xs
      x -> [x]

---- utility functions
lex, kw :: Parser a -> Parser a
lex p = p <* skipMany (hidden " ") -- FIXME: hspace?
kw p = lex $ try $ p <* lookAhead (space1 <|> eof)
ln :: Parser ()
ln = eol >> skipMany (choice
  [ void $ "%" >> skipManyTill anySingle eol
  , hidden space1
  ])

linesOf :: Parser a -> Parser [a]
linesOf p = space *> some (p <* (ln <|> lookAhead eof)) <* eof
