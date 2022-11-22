module ProofChecker
  ( Facts
  , checkProof
  , matchEx
  , mergeVars
  ) where


import Control.Monad (foldM, zipWithM)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

import Types

type Facts = Map PropName Prop

checkProof :: Facts -> Prop -> Proof -> Either String ()
checkProof facts (Prop{..}) proof = proofLoop from proof
 -- unify to conclusion and check existentials
  where
    proofLoop cxt = \case
      [] -> Left "proof is empty"
      _ -> Left "proof checker is not implemented"

checkBlock :: Facts -> [Expr] -> ProofBlock -> Either String ()
checkBlock facts cxt = \case
  Infer expr ""
    | expr `elem` cxt -> Right ()
    | otherwise -> Left "can't infer expression from context"
    -- search the exact expr in the context
  Infer expr ref -> case Map.lookup ref facts of
    Nothing -> Left "can't find referenced statement"
    Just (Prop{..}) -> Left "not implemented"
      -- try to unify with consequent
      -- replace unified variables in antecendent and prove antecendent
        -- var is free if not in mapping
  _ -> Left "not implemented yet"


type VarMap = Map Char Char

-- Get a variables to variables mapping that converts from ex1 to ex2.
-- Fails if it is not possible to convert ex1 to ex2 due to:
--  - mismatching functors: EQAB -> NECD
--  - conflicting variables: EQAA -> EQAB
matchEx :: Expr -> Expr -> Either String VarMap
matchEx ex1 ex2 = case (ex1, ex2) of
  (AN xs, AN ys)
    | length xs == length ys -> zipWithM matchEx xs ys >>= mergeVars
  (OR xs, OR ys)
    | length xs == length ys -> zipWithM matchEx xs ys >>= mergeVars
  (Fun f xs, Fun g ys)
    | f == g && length xs == length ys -> mergeVars $ zipWith Map.singleton xs ys
  _ -> Left $ "can't match " ++ show ex1 ++ " with " ++ show ex2


-- Merges list of mappings.
-- Fails if there are conflicts in mappings
-- (e.g. [a->b] in one mapping and [a->c] in another).
mergeVars :: [VarMap] -> Either String VarMap
mergeVars = foldM f Map.empty . concatMap Map.toList
  where
    f m (k,x) = case Map.lookup k m of
      Nothing -> pure $ Map.insert k x m
      Just y
        | x == y -> pure m
        | otherwise -> Left $ "conflicting mappings: " ++ show (k, (x, y))
