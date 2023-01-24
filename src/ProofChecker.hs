module ProofChecker
  ( Facts
  , ProofCheckerErr(..)
  , checkProof
  -- vvv-- exported for testing only
  , inferExact
  , inferExact'
  , inferWithEqs
  , inferWithEqs'
  , inferWithProp'
  , rewriteAs
  , mergeVars
  ) where

import Prelude hiding (Ordering(..))
import Control.Monad (forM_, foldM, zipWithM, when)
import Data.List (nub)
import Data.Either (rights, isRight)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set

import Types
import Utils


type Context = [Expr]
type Facts = Map PropName Prop
type VarMap = Map Char Char


-- | Check a proof of a proposition.
-- The proof can reference some of already proved facts.
-- Returns error if proof is not valid.
checkProof :: Facts -> Prop -> Proof -> Result ()
checkProof facts p@(Prop{..}) proof
  = withErrContext ("proving prop " ++ show p) $ do
    -- Initial context contains expressions from the antecedent.
    provedExprs <- checkAllBlocks facts antecedent proof
    when (not $ consequent `canBeProvedFrom` provedExprs)
      $ throwStr "Can't prove consequent from the context"


-- Iterate over proof blocks checking each with the context containing
-- already proved intermediate expressions.
checkAllBlocks :: Facts -> Context -> [ProofBlock] -> Result Context
checkAllBlocks facts startCxt blocks = do
    let foldProofBlocks cxt chkBlk = foldM chkBlk cxt blocks
    foldProofBlocks startCxt $ \cxt block -> do
      provedExpr <- withErrContext ("checking block " ++ show block)
        $ checkBlock facts cxt block
      -- If provedExpr is a conjunction we add all its conjuncts
      -- separately. E.g. proving BEACE in 3.7.a.prf:
      --    ANBEACE+EECECD  postulate:extension
      --    BEACE
      pure $ conjuncts provedExpr ++ cxt


checkBlock :: Facts -> Context -> ProofBlock -> Result Expr
checkBlock facts cxt = \case
  -- Search the exact expr in the context.
  Infer expr "" -> inferExact' cxt expr >> pure expr

  -- This is a meta-axiom. It searches EQs in the context and applies them
  -- to the expr.
  Infer expr "cn:equalitysub" -> inferWithEqs' cxt expr >> pure expr

  -- Search the referenced proposition among facts and try to satisfy it from
  -- the context.
  Infer expr ref -> case Map.lookup ref facts of
    Nothing -> throwStr "can't find the referenced statement"
    Just prop -> withErrContext ("with prop " ++ show prop)
      $ inferWithProp' cxt prop expr >> pure expr

  Reductio assumption conclusion proof -> do
    when (assumption /= negated conclusion)
      $ throwStr "Assumption must be a negation of the conclusion"

    let startCxt = assumption : cxt
    cxt' <- checkAllBlocks facts startCxt proof
    if notConsistent cxt'
      then pure conclusion
      else throwStr "No contradiction found"

  -- Disjunction of cases must be true in the context. There are two
  -- options: it can be inferred or it is exhaustive i.e. `A or not A`.
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


-- We have two versions of each `infer*` function:
--  - the one without a tick holds inference logic;
--  - the one with a tick handles cases with complex AND/OR expressions and
--  eventually calls the tickless version one or more times.

inferExact' :: Context -> Expr -> Result ()
inferExact' cxt expr = inferExact cxt expr
  `orElse` (\err -> case expr of
    AN exs -> allE $ map (inferExact' cxt) exs
    OR exs -> anyE $ map (inferExact' cxt) exs
    _ -> Left err)

inferExact :: Context -> Expr -> Result ()
inferExact cxt ex = when (not $ ex `elem` cxt)
  $ throwStr "can't infer expression from the context"

inferWithEqs' :: Context -> Expr -> Result ()
inferWithEqs' cxt expr = inferWithEqs cxt expr
  `orElse` (\err -> case expr of
    AN exs -> allE $ map (inferWithEqs' cxt) exs
    OR exs -> anyE $ map (inferWithEqs' cxt) exs
    _ -> Left err)

inferWithEqs :: Context -> Expr -> Result ()
inferWithEqs cxt expr = do
  let equalities = concatMap
        (\case { Fun EQ [a,b] -> [(a,b), (b,a)] ; _ -> [] })
        cxt

  let isEqMap -- maps only equals to equals
        = all (`elem` equalities)
        . Map.toList . Map.filterWithKey (/=)

  let rewrites
        = filter isEqMap $ rights
        -- We need to try to rewrite in both directions. Here is an example:
        -- 1) inferWithEqs [EQAB, COABC] COAAC
        -- 2) inferWithEqs [EQAB, COAAC] COABC
        -- In both cases COABC and COAAC are equivalent due to EQAB but
        -- `rewriteAs` is unaware of that equality, so this fails:
        --    COAAC `rewriteAs` COABC = [A->A, A->B] = FAIL
        -- but the reverese succeeds:
        --    COABC `rewriteAs` COAAC = [A->A, B->A]
        $ map (`rewriteAs` expr) cxt ++ map (expr `rewriteAs`) cxt

  when (null rewrites)
    $ withErrContext ("equalities found " ++ show equalities)
      $ withErrContext ("provedExprs " ++ show cxt)
      $ throwStr "Can't find how to rewrite with equalities"


inferWithProp' :: Context -> Prop -> Expr -> Result ()
inferWithProp' cxt prop expr
  = infer prop
    `orElse` (\case
      _ | isEquality prop -> withErrContext ("rev prop") $ infer (rev prop)
      err -> Left err)
  where
    -- Collect all variables used in the context.
    knownVars = let getVars = foldMap Set.singleton in foldMap getVars cxt
    conflict var = var `Set.member` knownVars

    infer (Prop{..}) = do
      -- Proposition is like an expression template in a sense that exact
      -- variable names are not important.
      --
      -- So for the first step we try to match proposition's consequent with
      -- the expression we want to prove. "To match" means to find a variable
      -- mapping that substitutes proposition's "template variables" with the
      -- names of real objects that are used in the context and the expression
      -- to prove.
      --
      -- A bit of complication adds that we have several options to prove an
      -- expression:
      --    - Exact match: consequent(varMap) = exp.
      --    - Consequent is of the form AND[ex1, ex2, ...]. This means that all
      --    of ex1, ex2, ... are true (proved) if we can prove proposition's
      --    antecendent. So we try to match exp with all AND subexpressions.
      --    - exp is of the form OR[ex1 ex2, ...]. In that case it is enough to
      --    prove any of the ex1, ... to prove exp.
      -- It is the same what we do in "ticked" inference functions `inferExact'`
      -- and `inferWithEqs'`. See tests for some exapmles.
      let baseMaps = consequent `rewriteWithSubexprs` expr
      when (null baseMaps)
        $ throwStr "can't match consequent with expr"

      -- Applying a proposition may introduce new variables into the scope.
      -- We need to ensure that they are not in conflict with already existing
      -- variables. E.g.:
      --   - with context [NExz, EQyz]
      --   - applying prop `NEac => ∃b . BEabc` to `BExyz`
      --   - will map `abc => xyz` where `y` must be a fresh variable but it
      --   is not as it is already used in the context.
      let newVars vm = catMaybes $ map (`Map.lookup` vm) existentialVars

      -- Filter out mappings that in conflict with `knownVars`.
      let baseMaps' = filter (not . any conflict . newVars) baseMaps
      when (null baseMaps')
        $ throwStr "conflict with existential vars"

      -- Now we are using the context to prove all conjuncts of the antecendent.
      -- Note the usage of ticked `rewriteWithSubexprs'`.
      let inferWithVarMap vm ex = rights
            [ mergeVars vm vm'
            | e <- cxt
            , vm' <- ex `rewriteWithSubexprs'` e
            ]

      let extMaps = do
            vm <- baseMaps'
            foldM inferWithVarMap vm antecedent

      when (null extMaps)
        $ withErrContext ("context " ++ show cxt)
        $ throwStr "can't prove antecendent from the context"


rewriteWithSubexprs :: Expr -> Expr -> [VarMap]
rewriteWithSubexprs ax bx = rights
  [ a `rewriteAs` b
  | a <- nub $ ax : conjuncts ax
  , b <- nub $ bx : disjuncts bx
  ]

rewriteWithSubexprs' :: Expr -> Expr -> [VarMap]
rewriteWithSubexprs' ax bx = rights
  [ a `rewriteAs` b
  | a <- nub $ ax : disjuncts ax
  , b <- nub $ bx : conjuncts bx
  ]


-- Here we mean "can be proved without referring to any axioms or facts".
canBeProvedFrom :: Expr -> Context -> Bool
canBeProvedFrom expr cxt = isRight $ inferExact' cxt expr

contradicts :: Expr -> [Expr] -> Bool
contradicts ex exs = negated ex `canBeProvedFrom` exs

-- Contains both some expression and its negation.
notConsistent :: Context -> Bool
notConsistent exs = any (`contradicts` exs) exs

isExhaustive :: [Expr] -> Bool
isExhaustive exs = all (`contradicts` exs) exs


-- Given two expressions ex1 and ex2, this functions computes a variables to
-- variables mapping that translates ex1 to ex2.
-- Example:
--    - COABC `rewriteAs` COCBA = [A->C, B->B, C->A]
-- Fails if it is not possible to convert ex1 to ex2 due to:
--    - mismatching functors: EQAB -> NECD
--    - conflicting variables: EQAA -> EQAB (maps A simultaneously to A and B)
--  NB!: Result of `rewriteAs` is a mapping which is not always injective.
--  E.g.
--    - COABC `rewriteAs` COXYX  = [A->X, B->Y, C->X] (both A and C map to X).
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


-- Merges multiple mappings into one or fails if there is a conflict
-- (e.g. [a->b] in one mapping and [a->c] in another).
mergeVars :: VarMap -> VarMap -> Result VarMap
mergeVars vm = foldM f vm . Map.toList
  where
    f m (k,x) = case Map.lookup k m of
      Nothing -> pure $ Map.insert k x m
      Just y
        | x == y -> pure m
        | otherwise -> throwStr $ "conflicting mappings: " ++ show (k, (x, y))
