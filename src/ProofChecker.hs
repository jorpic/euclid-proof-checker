module ProofChecker
    ( parseExpr
    , unify, unify'
    , negate
    , implies
    ) where

import Prelude hiding (Ordering(..), negate)
import Control.Monad (foldM)
import Data.List.Split (splitOn)
import Data.Map (Map)
import Data.Map qualified as Map

import Expr

guardE :: Bool -> String -> Result ()
guardE c err = if c then Right () else Left err

withContext :: String -> Result a -> Result a
withContext cxt = \case
  Left err -> Left $ cxt <> unlines (map ("\n\t" <>) $ lines err)
  r -> r

parseExpr :: String -> Result Expr
parseExpr txt
  = withContext ("parsing expr: " <> txt)
  $ do
    guardE (length txt >= 2) "no functor found"
    let (fn, xs) = splitAt 2 txt
    fn' <- case reads fn of
      [(x,"")] -> pure x
      _ -> Left $ "invalid functor: " <>  show fn
    xs' <- case fn' of
      NO -> (:[]) <$> parseExpr xs
      AN -> sequence (map parseExpr $ splitOn "+" xs)
      OR -> sequence (map parseExpr $ splitOn "|" xs)
      _ | length xs /= arity fn'
        -> Left "number of arguments does not match functor arity"
      _ -> pure $ map Atom xs
    pure $ Expr fn' xs'

e2m :: Either a b -> Maybe b
e2m = either (const Nothing) Just

unify' :: Expr -> [Expr] -> Maybe (Map Char Char)
unify' _ [] = Nothing
unify' p [q] = e2m $ unify p q
unify' p qs  = e2m $ unify p $ Expr AN qs

type UniMap = Map Char Char
type Result a = Either String a

unify :: Expr -> Expr -> Result UniMap
unify p q
  = withContext ("unify:" <> show p <> " ~ " <> show q)
  $ case (p,q) of
    (Atom x, Atom y)
      -> pure $ Map.singleton y x
    (Expr f fx, Expr g gx) -> do
      guardE (f == g) "functors do not match"
      guardE (length fx == length gx) "functor arities do not match"
      uniMaps <- sequence (zipWith unify fx gx)
      foldM mergeMaps Map.empty uniMaps
    _ -> Left "cant' match functor with atom"

mergeMaps :: UniMap -> UniMap -> Result UniMap
mergeMaps mx = go mx . Map.toList
  where
    go mx' [] = Right mx'
    go mx' ((ky, vy):ys) = case Map.lookup ky mx' of
      Just vx
        | vx == vy  -> go mx' ys
        | otherwise -> Left $ "conflict: " <> show (ky, [vx, vy])
      Nothing -> go (Map.insert ky vy mx') ys


negate :: Expr -> Result Expr
negate (Atom{}) = Left "can't negate an atom"
negate (Expr fn xs) = case fn of
  AN -> Expr OR <$> mapM negate xs
  OR -> Expr AN <$> mapM negate xs
  EQ -> pure $ Expr NE xs
  NE -> pure $ Expr EQ xs
  CO -> pure $ Expr NC xs
  NC -> pure $ Expr CO xs
  NO -> pure $ head xs
  _  -> pure $ Expr NO [Expr fn xs]


implies :: Expr -> Expr -> Expr -> Result Bool
implies (Expr EQ [x,y]) (Expr f rs) (Expr g ps)
  = pure
  $  f == g
  && length rs == length ps
  && and [
         (r == p)
      || (r == x && p == y)
      || (r == y && p == x)
    | (r, p) <- zip rs ps
    ]
implies eq r p = Left $ "wrong args for implies" <> show (eq, r, p)
