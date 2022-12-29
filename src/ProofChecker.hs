{-# LANGUAGE TemplateHaskell #-}
module ProofChecker
  ( Facts
  , checkProof
  , rewriteAs
  , mergeVars
  ) where

import Prelude hiding (Ordering(..))
import Control.Exception
import Control.Monad (forM_, foldM, zipWithM, (>=>), when)
import Data.Either (rights)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set

import Types
import Utils (mapLeft)


type Context = [Expr]
type Facts = Map PropName Prop
type VarMap = Map Char Char

data ProofCheckerErr = StringErr { errs ::  [String] }
  deriving Exception

instance Show ProofCheckerErr where
  show = unlines . zipWith indent [0..] . errs
    where
      indent i = (replicate (i*2) ' ' ++)

type Result a = Either ProofCheckerErr a

throwStr :: String -> Result a
throwStr = Left . StringErr . (:[])

withErrContext :: String -> Result a -> Result a
withErrContext cxt = mapLeft $ StringErr . (cxt:) . errs

-- | Check a proof of a proposition.
-- The proof can reference some of already proved facts.
-- Returns error if proof is not valid.
checkProof :: Facts -> Prop -> Proof -> Result ()
checkProof facts p@(Prop{..}) proof
  = withErrContext ("when proving " ++ show p) $ do
    -- Initial context contains expressions from the antecedent.
    provedExprs <- checkAllBlocks facts antecedent proof
    when (not $ consequent `canBeProvedFrom` provedExprs)
      $ throwStr "Can't prove consequent"


checkBlock :: Facts -> Context -> ProofBlock -> Result Expr
checkBlock facts cxt blk
  = withErrContext (show blk)
  $ case blk of
    -- Search the exact expr in the context.
    Infer expr ""
      | expr `canBeProvedFrom` cxt -> pure expr
      | otherwise -> throwStr "can't infer expression from the context"

    -- This is a meta-axiom. It searches EQs in context and tries to
    -- apply substitution.
    Infer expr "cn:equalitysub" -> inferEqSubstitution cxt expr

    -- Search the referenced proposition among facts and try to satisfy it from
    -- the context.
    Infer expr ref -> case Map.lookup ref facts of
      Nothing -> throwStr "can't find the referenced statement"
      Just prop -> withErrContext ("with prop " ++ show prop)
        $ inferConjWithProp cxt prop expr

    Reductio assumption conclusion proof -> do
      when (assumption /= negated conclusion)
        $ throwStr "Assumption must be a negation of the conclusion"

      let startCxt = assumption : cxt
      cxt' <- checkAllBlocks facts startCxt proof
      if notConsistent cxt'
        then pure conclusion
        else throwStr "No contradiction found"

    -- Disjunction of cases must be true in the context. There are two
    -- options: it can be inferred or it is exhaustive i.e. (A or not A).
    Cases expr casesAndProofs -> do
      let cases = map fst casesAndProofs
      when (not $ OR cases `canBeProvedFrom` cxt || isExhaustive cases)
        $ throwStr "Cases are not exhaustive and cannot be inferred"

      forM_ casesAndProofs $ \(cse, proof) ->
        withErrContext ("case " ++ show cse) $ do
          cxt' <- checkAllBlocks facts (cse : cxt) proof
          when (not $ expr `canBeProvedFrom` cxt')
            $ throwStr $ "can't infer " ++ show expr
      pure expr


inferEqSubstitution :: Context -> Expr -> Result Expr
inferEqSubstitution cxt expr = do
      let equalities = concatMap
            (\case { Fun EQ [a,b] -> [(a,b), (b,a)] ; _ -> [] })
            cxt
      -- maps only equals to equals
      let isEqMap
            = all (`elem` equalities)
            . Map.toList . Map.filterWithKey (/=)
      let rewrites
            = filter isEqMap $ rights
            -- FIXME: explain this ----vvvvvv
            $ map (`rewriteAs` expr) cxt ++ map (expr `rewriteAs`) cxt
      when (null rewrites)
        $ withErrContext ("equalities found " ++ show equalities)
          $ withErrContext ("provedExprs " ++ show cxt)
          $ throwStr "Can't find how to rewrite with equalities"
      pure expr


inferConjWithProp :: Context -> Prop -> Expr -> Result Expr
inferConjWithProp provedExprs prop expr = do
  -- If prop's consequent is a conjunction we should try
  -- to match expr with each conjunct.
  let matches =
        [ inferWithProp provedExprs p expr
        | e <- conjuncts $ consequent prop
        , let p = prop {consequent = e}
        ]
  case rights matches of
    ex : _ -> pure ex
    -- FIXME: redundancy here
    -- try to match the whole consequent with expr
    [] -> inferWithProp provedExprs prop expr

inferWithProp :: Context -> Prop -> Expr -> Result Expr
inferWithProp provedExprs Prop{..} expr = do
  -- Variable mapping that unifies 'consequent' with the expression to be
  -- proved.
  varMap <- consequent `rewriteAs` expr

  -- For each expression in 'antecedent', find an expression in the context
  -- such that both can be unified by a variable mapping.
  -- All those mappings must be compatible with each other and with 'varMap'.
  let possibleMappings = foldM (searchEx provedExprs) varMap antecedent
  -- ^ List monad is used to search repeatedly and backtrack in case of conflict.
  extendedVarMap <- case possibleMappings of
    vm : _ -> pure vm
    [] -> withErrContext ("base map " ++ show varMap)
      $ throwStr $ "can't prove prop from context " ++ show provedExprs

  -- New objects may be introduced by the proposition.
  -- Rename them according to 'extendedVarMap'.
  let newObjects = catMaybes $ map (`Map.lookup` extendedVarMap) existentialVars
  -- ^ 'catMaybes' is fine here because 'Nothing' occurs only if there is
  -- some variable that is mentioned in 'existentialVars' but not used in
  -- the antecedent.

  let getExprObjects = foldMap Set.singleton
  let knownObjects = foldMap getExprObjects provedExprs
  if any (`Set.member` knownObjects) newObjects
    then throwStr $ "Some of the new objects clash with known ones: "
      ++ show newObjects
    else rename extendedVarMap consequent


-- Iterate over proof blocks checking each with the context containing
-- already proved intermediate expressions.
checkAllBlocks :: Facts -> Context -> [ProofBlock] -> Result Context
checkAllBlocks facts startCxt blocks = do
    let foldProofBlocks cxt chkBlk = foldM chkBlk cxt blocks
    foldProofBlocks startCxt $ \cxt block -> do
      provedExpr <- checkBlock facts cxt block
      -- If provedExpr is a conjunction we add all its conjuncts
      -- separately. E.g. proving BEACE in 3.7.a.prf:
      --    ANBEACE+EECECD  postulate:extension
      --    BEACE
      pure $ conjuncts provedExpr ++ cxt


rename :: VarMap -> Expr -> Result Expr
rename varMap expr = case traverse (`Map.lookup` varMap) expr of
  Just expr' -> pure expr'
  Nothing -> throwStr "Impossible! Failed to apply varMap."

-- If ex is a conjunction, we explode it and try to prove each conjunct
-- separately.
canBeProvedFrom :: Expr -> Context -> Bool
canBeProvedFrom ex cxt = all (`elem` cxt) $ conjuncts ex

-- Contains both some expression and its negation.
notConsistent :: Context -> Bool
notConsistent exprs = maximum [negated e `elem` exprs | e <- exprs]

-- This is oversimplification but will do for our purposes.
isExhaustive :: [Expr] -> Bool
isExhaustive [a,b] = a == negated b
isExhaustive _ = False

-- In the provided context search all expressions that can be matched to `ex` without
-- a conflict with the var map `vm`.
searchEx :: Context -> VarMap -> Expr -> [VarMap]
searchEx cxt vm ex
  = rights
  $ map ((ex `rewriteAs`) >=> mergeVars vm) cxt


-- findMatching :: [Expr] -> Expr -> [(Expr, VarMap)]
-- dropConflictingTo :: VarMap -> [(Expr, VarMap)] -> [(Expr, VarMap)]


-- Get a varables to variables mapping that converts from ex1 to ex2.
--  `ex1[varMap] = ex2`.
-- Fails if it is not possible to convert ex1 to ex2 due to:
--  - mismatching functors: EQAB -> NECD
--  - conflicting variables: EQAA -> EQAB
--  NB!: Result of `matchEx` is a mapping which is not always injective.
--    E.g. in `matchEx COABC COXYX  => {A: X, B: Y, C: X}`
--    both A and C map to X.
--    Switching arguments would result in variable conflict (non-deterministic
--    mapping).
rewriteAs :: Expr -> Expr -> Result VarMap
rewriteAs ex1 ex2 = case (ex1, ex2) of
  (AN xs, AN ys) | length xs == length ys -> rewriteMany xs ys
  (OR xs, OR ys) | length xs == length ys -> rewriteMany xs ys
  (NO x,  NO y) -> x `rewriteAs` y
  (Fun f xs, Fun g ys)
    | f == g && length xs == length ys
      -> mergeMany $ zipWith Map.singleton xs ys
  _ -> throwStr $ "can't match " ++ show ex1 ++ " with " ++ show ex2
  where
    mergeMany = foldM mergeVars Map.empty
    rewriteMany xs ys = zipWithM rewriteAs xs ys >>= mergeMany


-- Merges list of mappings.
-- Fails if there are conflicts in mappings
-- (e.g. [a->b] in one mapping and [a->c] in another).
mergeVars :: VarMap -> VarMap -> Result VarMap
mergeVars vm = foldM f vm . Map.toList
  where
    f m (k,x) = case Map.lookup k m of
      Nothing -> pure $ Map.insert k x m
      Just y
        | x == y -> pure m
        | otherwise -> throwStr $ "conflicting mappings: " ++ show (k, (x, y))
