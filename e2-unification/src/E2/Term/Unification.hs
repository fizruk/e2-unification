{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RecordWildCards            #-}
module E2.Term.Unification where

import           Data.Coerce          (coerce)
import           Debug.Trace
import           Unsafe.Coerce

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Logic
import           Control.Monad.State
import           Control.Monad.Writer
import qualified Data.Bifunctor
import           Data.List            (elemIndex, inits, isSuffixOf, nub, tails)
import           Data.Void

import           Control.Monad.Fresh
import           E2.Rule
import           E2.Term

-- | Quantify over arbitrarily many variables using 'Inc'.
data Forall t var
  = Forall (Forall t (Inc var)) -- ^ \(\forall x. C\)
  | Ground (t var)              -- ^ Ground term/constraint (no quantifiers).

instance (forall a. Eq a => Eq (t a), Eq var) => Eq (Forall t var) where
  Forall t == Forall t' = t == t'
  Ground t == Ground t' = t == t'
  _ == _                = False

instance (forall a. Show a => Show (t a), Show var) => Show (Forall t var) where
  show (Forall t) = "Forall (" <> show t <> ")"
  show (Ground t) = "Ground (" <> show t <> ")"

instance Functor t => Functor (Forall t) where
  fmap f (Forall t) = Forall (fmap (fmap f) t)
  fmap f (Ground t) = Ground (fmap f t)

instance Foldable t => Foldable (Forall t) where
  foldMap f (Forall t) = foldMap (foldMap f) t
  foldMap f (Ground t) = foldMap f t

instance Traversable t => Traversable (Forall t) where
  traverse f (Forall t) = Forall <$> traverse (traverse f) t
  traverse f (Ground t) = Ground <$> traverse f t

-- | A ground constraint has no quantifiers.
data GroundConstraint metavar var
  = Term metavar var :==: Term metavar var  -- ^ \( t \stackrel{?}{=} u\)
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | A constraint is a ground constraint put under some number of quantifiers.
--
-- \(\forall \overline{x_k}. t \stackrel{?}{=} u\)
type Constraint metavar = Forall (GroundConstraint metavar)

-- | Apply meta substitutions to a given constraint.
applySubsts :: Eq m => MetaSubsts m a -> Constraint m a -> Constraint m a
applySubsts substs = \case
  Forall c          -> Forall (applySubsts (S <$> substs) c)
  Ground (t :==: s) -> Ground (f t :==: f s)
  where
    f = substituteMeta' $ \m ->
          case lookup m (toLookupList substs) of
            Nothing -> Nothing
            Just t' -> Just t'

-- | The unification context (a combination of backtracking and fresh name supply).
newtype Unify v a = Unify { runUnify :: LogicT (Fresh v) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadFail, MonadFresh v, MonadLogic)

-- | Run a unification computation using default fresh name supply
-- and extracting the first result.
--
-- NOTE: will throw an exception when no solution is available.
defaultUnify :: Unify Variable a -> a
defaultUnify = head . flip evalFresh defaultVars . observeManyT 10 . runUnify
  where
    defaultVars = [ Variable ("m" ++ toSub n) | n <- [0..] ]
    toSub = map toSubDigit . show
    mappings = zip "0123456789" "₀₁₂₃₄₅₆₇₈₉"
    toSubDigit d =
      case lookup d mappings of
        Nothing -> '.'
        Just c  -> c

-- | Run a unification computation using default fresh name supply
-- and extracting all results.
--
-- NOTE: will throw an exception when no solution is available.
defaultUnifyAll :: Unify Variable a -> [a]
defaultUnifyAll = flip evalFresh defaultVars . observeAllT . runUnify
  where
    defaultVars = [ Variable ("m" ++ toSub n) | n <- [0..] ]
    toSub = map toSubDigit . show
    mappings = zip "0123456789" "₀₁₂₃₄₅₆₇₈₉"
    toSubDigit d =
      case lookup d mappings of
        Nothing -> '.'
        Just c  -> c

-- * \(E^2\)-unification procedure

data Simplifications a = Simplifications
  { simplifyDelete     :: a
  , simplifyRigidRigid :: a
  , simplifyFlex       :: a
  , simplifyMutateMeta :: a
  } deriving (Functor, Foldable, Traversable)

instance Applicative Simplifications where
  pure x = Simplifications x x x x
  Simplifications f g h k <*> Simplifications x y z w =
    Simplifications (f x) (g y) (h z) (k w)

tryE2'
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [Rule m Void]    -- ^ Set \(R\) of rewrite rules.
  -> [Constraint m a] -- ^ Collection of constraints to simplify.
  -> f (String, [Constraint m a], MetaSubsts m a)
tryE2' _ [] = pure mempty
tryE2' rules constraints = do
  Simplifications{..} <- sequenceA <$>
    traverse (uncurry $ try rules) (splits constraints)
  once (asum simplifyDelete) `orElse`
    (firstNonEmpty simplifyRigidRigid
      <|> firstNonEmpty simplifyFlex
      <|> firstNonEmpty simplifyMutateMeta)

firstNonEmpty :: MonadLogic f => [f a] -> f a
firstNonEmpty [] = empty
firstNonEmpty (m:ms) = do
  msplit m >>= \case
    Nothing      -> firstNonEmpty ms
    Just (x, xs) -> pure x <|> xs

asum :: (Alternative f, Foldable t) => t (f a) -> f a
asum = foldr (<|>) empty

data IsFound = NotFound | Found

-- | Ensure that at least one element in a 'Traversable' container
-- is not 'empty'. Returns new container with the same contents,
-- but computed results (until the first non-empty element).
--
-- >>> ensureExists' [empty <|> empty, pure 3, empty <|> pure 1] :: [[[Int]]]
-- [[[],[3],[1]]]
--
-- >>> ensureExists' [empty <|> empty, empty, empty] :: [[[Int]]]
-- []
ensureExists'
  :: (MonadPlus f, MonadLogic f, Traversable t)
  => t (f a)
  -> f (t (f a))
ensureExists' t = flip evalStateT NotFound $ do
  t' <- traverse k t
  get >>= \case
    NotFound -> lift empty
    Found    -> return t'
  where
    k :: (MonadPlus f, MonadLogic f) => f a -> StateT IsFound f (f a)
    k x = get >>= \case
      NotFound -> (do
        x' <- lift $ ensureExists x
        put Found
        return x') `orElse` return empty
      Found -> return x

ensureSimplificationExists
  :: (MonadPlus f, MonadLogic f)
  => Simplifications (f a)
  -> f (Simplifications (f a))
ensureSimplificationExists = ensureExists'

ensureExists :: MonadLogic f => f a -> f (f a)
ensureExists m =
  msplit m >>= \case
    Nothing      -> empty
    Just (x, xs) -> return (pure x <|> xs)

try
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [Rule m Void]    -- ^ Set \(R\) of rewrite rules.
  -> Constraint m a   -- ^ A constraint to simplify.
  -> [Constraint m a] -- ^ Other constraints (to preserve).
  -> f (Simplifications (f (String, [Constraint m a], MetaSubsts m a)))
try rules c cs' = ensureSimplificationExists $
  Simplifications
    { simplifyDelete      = tryDeleteEliminate
    , simplifyRigidRigid  = tryRigidRigid
    , simplifyFlex        = tryFlex
    , simplifyMutateMeta  = tryMutateMeta
    }
  where
    tryDeleteEliminate = do
      (ruleName, cs'', substs) <- upgrade (\c' _bvars -> delete c' <|> eliminate c') c -- <|> eliminate c') c
      return (ruleName, cs'' <> map (applySubsts substs) cs', substs)

    tryRigidRigid = do
      guard (isRigidRigid c)
      (ruleName, cs'', substs) <- upgrade (\c' bvars -> decompose c' <|> mutate rules bvars c') c
      return (ruleName, cs'' <> map (applySubsts substs) cs', substs)

    tryFlex = do
      (ruleName, cs'', substs) <- upgrade (\c' _bvars -> project c' <|> imitate c') c
      return (ruleName, cs'' <> map (applySubsts substs) cs', substs)

    tryMutateMeta = do
      (ruleName, cs'', substs) <- upgrade (\c' bvars -> mutateMeta rules bvars c') c
      return (ruleName, cs'' <> map (applySubsts substs) cs', substs)

    upgrade = convert . go []

    convert k c' = do
      (ruleName, cs, substs) <- k (fmap F c')
      cs'' <- traverse (traverse removeIncMany) cs
      substs' <- traverse removeIncMany substs
      return (ruleName, cs'', substs')

--     go :: [Term m (IncMany a)]
--        -> (GroundConstraint m (IncMany a) -> [Term m (IncMany a)] -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a)))
--        -> Constraint m (IncMany a)
--        -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
    go bvars k (Ground c') = k c' bvars
    go bvars k (Forall c') = do
      (ruleName, cs, substs) <- go (Var (joinInc Z) : map (fmap (joinInc . S)) bvars) k (joinInc <$> c')
      cs'' <- traverse (traverse decIncMany) cs
      substs' <- traverse decIncMany substs
      return (ruleName, cs'', substs')

-- | Attempt applying one step of \(E^2\)-unification to a collection of constraints.
--
-- This will try to simplify constraints in the following way:
--
-- 0. If there are no constraints to simplify, then exit successfully.
-- 1. Apply 'delete' or 'eliminate' rule to some constraint if possible.
-- 2. Simplify any rigid-rigid constraint with 'decompose' or 'mutate' rules.
-- 3. Otherwise, apply 'project', 'imitate', or 'mutateMeta' rules.
-- tryE2
--   :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
--   => [Rule m Void]    -- ^ Set \(R\) of rewrite rules.
--   -> [Constraint m a] -- ^ Collection of constraints to simplify.
--   -> f (String, [Constraint m a], MetaSubsts m a)
-- tryE2 _ [] = pure mempty
-- tryE2 rules constraints =
--   -- apply delete and eliminate rules first (deterministic)
--   once (tryDeleteEliminate constraints) `orElse`
--     -- then solve rigid-rigid constraints (non-deterministic)
--     tryRigidRigid constraints <|> -- `orElse`
--       -- finally, solve flex-rigid and flex-flex constraints
--       tryFlex constraints
--   where
--     tryDeleteEliminate cs = do
--       (c, cs') <- selectOne cs
--       (ruleName, cs'', substs) <- upgrade (\c' _bvars -> delete c') c -- <|> eliminate c') c
--       return (ruleName, cs'' <> map (applySubsts substs) cs', substs)
--
--     tryRigidRigid cs = do
--       (c, cs') <- selectOne cs
--       guard (isRigidRigid c)
--       (cs'', substs) <- upgrade (\c' bvars -> decompose c' <|> mutate rules bvars c') c
--       return (cs'' <> map (applySubsts substs) cs', substs)
--
--     tryFlex cs = do
--       (c, cs') <- selectOne cs
--       (cs'', substs) <- upgrade (\c' bvars -> project c' <|> imitate c' <|> mutateMeta rules bvars c') c
--       return (cs'' <> map (applySubsts substs) cs', substs)
--
--     upgrade = convert . go []
--
--     convert k c = do
--       (cs, substs) <- k (fmap F c)
--       cs' <- traverse (traverse removeIncMany) cs
--       substs' <- traverse removeIncMany substs
--       return (cs', substs')
--
-- --     go :: [Term m (IncMany a)]
-- --        -> (GroundConstraint m (IncMany a) -> [Term m (IncMany a)] -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a)))
-- --        -> Constraint m (IncMany a)
-- --        -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
--     go bvars k (Ground c) = k c bvars
--     go bvars k (Forall c) = do
--       (cs, substs) <- go (Var (joinInc Z) : map (fmap (joinInc . S)) bvars) k (joinInc <$> c)
--       cs' <- traverse (traverse decIncMany) cs
--       substs' <- traverse decIncMany substs
--       return (cs', substs')


-- | Perform unificiation procedure, using DFS
-- and limiting search to a fixed maximum depth.
-- If maximum depth is reached, but not all constraints are simplified,
-- leftover constraints are returned along with intermediate substitution.
unifyDFS
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => Int              -- ^ Maximum search depth.
  -> [Rule m Void]    -- ^ Set \(R\) of rewrite rules.
  -> [Constraint m a] -- ^ Collection of constraints.
  -> f ([Constraint m a], MetaSubsts m a)
unifyDFS maxDepth rules = go 0
  where
    go _depth [] = -- trace (replicate (depth * 1) ' ' <> "solution found") $
      return mempty
    go depth constraints
      | depth >= maxDepth = -- trace (replicate (depth * 1) ' ' <> "max depth reached!") $
          pure (constraints, mempty)
      | otherwise = notrace (replicate (depth * 1) ' ' <> "[" <> show depth <> "] " <> ppConstraints' (unsafeCoerce constraints)) $ do
          (ruleName, cs, substs) <- tryE2' rules constraints
          (cs', substs') <-
            if (depth + 1 >= maxDepth && not (null cs))
               then trace (replicate (depth * 1) ' ' <> "[stop] " <> ruleName) $ go (depth + 1) cs
               else trace (replicate (depth * 1) ' ' <> ruleName) $ go (depth + 1) cs
          return (cs', substs' <> substs)

-- | Perform unificiation procedure, using k-depth DFS
-- and limiting search to a fixed maximum depth and BFS iterations.
-- If maximum depth is reached, but not all constraints are simplified,
-- these solutions are discarded.
unifyBFSviaDFS
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => Int  -- ^ Number of DFS interations.
  -> Int  -- ^ Max depth per one DFS iteration.
  -> [Rule m Void]    -- ^ Set \(R\) of rewrite rules.
  -> [Constraint m a] -- ^ Collection of constraints.
  -> f (MetaSubsts m a)
unifyBFSviaDFS maxIterations maxDepth rules = fmap . clean <*> go 0
  where
    go n [] = notrace ("solution found at depth = " <> show n) $
      pure mempty
    go n constraints
      | n >= maxIterations = empty
      | otherwise = do
          tryClose (unifyDFS maxDepth rules constraints) >>= \case
            Left incompletes -> notrace (replicate (2 * n) ' ' <> "after iteration " <> show (n + 1) <> " we have " <> show (length incompletes) <> " incomplete branches") $ do
              (cs, substs) <- choose incompletes
              substs' <- go (n + 1) cs
              return (substs' <> substs)
            Right substs -> notrace ("solution found on iteration = " <> show (n + 1)) $
              pure substs

    -- leave only substitutions for metavariables that occur in the original constraints
    clean constraints (MetaSubsts substs) = MetaSubsts (filter isOriginalMeta substs)
      where
        metas = foldMap constraintMetaVars constraints
        isOriginalMeta MetaSubst{..} = metaSubstVar `elem` metas

-- | Attempt to find a solution without any leftover constraints.
-- If such a solution exists, return corresponding substitution (using 'Right').
-- Otherwise, collect all partial solutions in a list (using 'Left').
tryClose
  :: MonadLogic f
  => f ([Constraint m a], MetaSubsts m a)
  -> f (Either [([Constraint m a], MetaSubsts m a)] (MetaSubsts m a))
tryClose m =
  msplit m >>= \case
    Nothing      -> pure (Left [])
    Just ((cs, substs), xs)
      | null cs   -> pure (Right substs) <|> tryClose xs  {- <|> do
          (cs', substs') <- xs
          guard (null cs')
          return (Right substs') -}
      | otherwise -> Data.Bifunctor.first ((cs, substs) :) <$> tryClose xs

-- | Extract all meta variables from a constraint.
constraintMetaVars :: Constraint m a -> [m]
constraintMetaVars (Forall c)           = constraintMetaVars c
constraintMetaVars (Ground (t :==: t')) = metavars t <> metavars t'

-- | Check if constraint is rigid-rigid (i.e. both sides are not meta variables).
isRigidRigid :: Constraint m a -> Bool
isRigidRigid (Forall c)                  = isRigidRigid c
isRigidRigid (Ground (MetaVar{} :==: _)) = False
isRigidRigid (Ground (_ :==: MetaVar{})) = False
isRigidRigid (Ground _)                  = True

-- * Pretty-printing

ppConstraints' :: [Constraint Variable Variable] -> String
ppConstraints' = unlines . map ppConstraint'

ppConstraint' :: Constraint Variable Variable -> String
ppConstraint' = ppConstraint defaultFreshVars getVariable

ppConstraint :: [String] -> (a -> String) -> Constraint Variable a -> String
ppConstraint freshVars ppVar = \case
  Forall c           ->
    case freshVars of
      []   -> error "not enough fresh variables"
      x:xs -> "forall " <> x <> "." <> ppConstraint xs (ppInc x . fmap ppVar) c
  Ground (t :==: t') -> ppTerm freshVars ppVar t <> " =?= " <> ppTerm freshVars ppVar t'

-- * \(E^2\)-unification rules

-- | Delete rule: \(\forall \overline{x_k}. t \stackrel{?}{=} t \longrightarrow \langle \varnothing, \mathsf{id} \rangle \)
delete
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f (String, [Constraint m (IncMany a)], MetaSubsts m (IncMany a))
delete = \case
  t :==: t'
    | t == t' -> notrace "[delete]" $ return ("delete", [], mempty)
  _ -> empty

-- | Decompose rule: \(\forall \overline{x_k}. F(\overline{t_n}, \overline{x.s_m}) \stackrel{?}{=} F(\overline{t'_n}, \overline{x.s'_m}) \longrightarrow \langle C_1 \cup C_2, \mathsf{id} \rangle \) where
--
-- * \( C_1 = \{ \forall \overline{x_k}. t_i \stackrel{?}{=} t'_i \) for all \(i = 1 \ldots n \}\)
-- * \( C_2 = \{ \forall \overline{x_k}, x. s_j \stackrel{?}{=} s'_j \) for all \(j = 1 \ldots m \}\)
decompose
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f (String, [Constraint m (IncMany a)], MetaSubsts m (IncMany a))
decompose = \case
  Con con args :==: Con con' args'
    | coerce (dropWhile (== '\'') . reverse) con == (coerce (dropWhile (== '\'') . reverse) con' :: String) && length args == length args' -> do
        args'' <- sequence $ zipWith mkConstraintArg args args'
        notrace ("[decompose] " <> show con) $ return ("decompose " <> show con, args'', mempty)
  _ -> empty
  where
    mkConstraintArg (Regular t) (Regular t') = return $ Ground (t :==: t')
    mkConstraintArg (Scoped s) (Scoped s')   = return $ Forall $ Ground (s :==: s')
    mkConstraintArg _ _ = mzero

-- | Eliminate rule: \(\forall \overline{x_k}. m[\overline{t_n}] \stackrel{?}{=} u \longrightarrow \langle \varnothing, \sigma \rangle \) where
--
-- * \(\sigma = [m[\overline{z_n} \mapsto u[\overline{t_n} \mapsto \overline{z_k}]]]\)
-- * \(\overline{t_k}\) is a list of distinct bound variables (from \(\overline{x_k}\))
-- * \(m\) does not occur in \(u\)
eliminate
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f (String, [Constraint m (IncMany a)], MetaSubsts m (IncMany a))
eliminate = \case
  -- eliminate (left)
  MetaVar m args :==: t
    | m `notElem` metavars t,
      Just zs <- distinctBoundVars args
      -> notrace "[eliminate (left)]" $ return ("eliminate (left)", [], MetaSubsts [metaSubst m (length args) (t >>= zs)])
  -- eliminate (right)
  t :==: MetaVar m args
    | m `notElem` metavars t,
      Just zs <- distinctBoundVars args
      -> notrace "[eliminate (right)]" $ return ("eliminate (right)", [], MetaSubsts [metaSubst m (length args) (t >>= zs)])
  _ -> empty

-- | Imitate rule: \(\forall \overline{x_k}. m[\overline{t_k}] \stackrel{?}{=} F(\overline{u_p}, \overline{x.s_q}) \longrightarrow \langle C_1 \cup C_2, \sigma \rangle \) where
--
-- * \(\sigma = [m[\overline{z_n}] \mapsto F(\overline{m_p[\overline{z_k}]}, \overline{x.m'_q[x, \overline{z_k}]})] \)
-- * \( C_1 = \{ \forall \overline{x_k}. m_i[\overline{t_k}] \stackrel{?}{=} u_i \) for all \(i = 1 \ldots p \}\)
-- * \( C_2 = \{ \forall \overline{x_k}, x. m'_j[x, \overline{t_k}] \stackrel{?}{=} s'_j \) for all \(j = 1 \ldots q \}\)
-- * \(\overline{m_p}, \overline{m'_q}\) are fresh meta variables
-- * \(m\) does not occur in \(\overline{u_p}\) or \(\overline{s_q}\)
imitate
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f (String, [Constraint m (IncMany a)], MetaSubsts m (IncMany a))
imitate = \case
  -- imitate (left)
  MetaVar m args :==: Con con args'
    | not (coerce ("'" `isSuffixOf`) con),
      m `notElem` (foldMap metavarsArg args') -> do
      (args'', constraints) <- runWriterT $ traverse (argTermToMetaVar args) args'
      notrace ("[imitate (left)] " <> show con) $ return ("imitate (left) " <> show con, constraints, MetaSubsts [metaSubst m (length args) (Con con args'')])
  -- imitate (right)
  Con con args' :==: MetaVar m args
    | not (coerce ("'" `isSuffixOf`) con),
      m `notElem` (foldMap metavarsArg args') -> do
      (args'', constraints) <- runWriterT $ traverse (argTermToMetaVar args) args'
      notrace ("[imitate (right)] " <> show con) $ return ("imitate (right) " <> show con, constraints, MetaSubsts [metaSubst m (length args) (Con con args'')])
  _ -> empty

-- | Project rule: \(\forall \overline{x_k}. m[\overline{t_k}] \stackrel{?}{=} u \longrightarrow \langle C, \sigma \rangle \) where
--
-- * \(\sigma = [m[\overline{z_n}] \mapsto z_i] \)
-- * \( C = \{ \forall \overline{x_k}. t_i \stackrel{?}{=} u \}\)
-- * \(m\) does not occur in \(u\)
project
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f (String, [Constraint m (IncMany a)], MetaSubsts m (IncMany a))
project = \case
  -- project (left)
  MetaVar m args :==: u
    | m `notElem` metavars u -> do
      i <- choose [0 .. length args - 1]
      let constraint = Ground (args !! i :==: u)
      notrace ("[project " ++ show (i + 1) ++ "/" ++ show (length args) ++ " (left)]") $
        return ("project " ++ show (i + 1) ++ "/" ++ show (length args) ++ " (left)", [constraint], MetaSubsts [metaSubst m (length args) (Var (B i))])
  -- project (right)
  MetaVar m args :==: u
    | m `notElem` metavars u -> do
      i <- choose [0 .. length args - 1]
      let constraint = Ground (args !! i :==: u)
      notrace "[project (right)]" $ return ("project " ++ show (i + 1) ++ "/" ++ show (length args) ++ " (right)", [constraint], MetaSubsts [metaSubst m (length args) (Var (B i))])
  _ -> empty

-- | Mutate rule: \(\forall \overline{x_k}. F(\overline{t_p}, \overline{x.s_q}) \stackrel{?}{=} u \longrightarrow \langle C_1 \cup C_2 \cup C_3, \mathsf{id} \rangle \) where
--
-- * \(F(\overline{l_p}, \overline{x.l'_q}) \to r\) is in \(R\)
-- * \( C_1 = \{ \forall \overline{x_k}. t_i \stackrel{?}{=} l_i \) for all \(i = 1 \ldots p \}\)
-- * \( C_2 = \{ \forall \overline{x_k}, x. s_j \stackrel{?}{=} l'_j \) for all \(j = 1 \ldots m \}\)
-- * \( C_3 = \{ \forall \overline{x_k}. r \stackrel{?}{=} u \} \)
mutate
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => [Rule m Void]
  -> [Term m (IncMany a)] -- bound variables (FIXME: handle better)
  -> GroundConstraint m (IncMany a)
  -> f (String, [Constraint m (IncMany a)], MetaSubsts m (IncMany a))
mutate rules boundVars = \case
  -- mutate (left)
  Con con args :==: u -> do
    Con con' args' :-> rhs <- choose rules >>= freshRule boundVars
    guard (con == con')
    guard (length args == length args')
    constraints <- flip traverse (zip args args') $ \case
      (Regular t, Regular l) -> pure (Ground (t :==: l))
      (Scoped s, Scoped l')  -> pure (Forall (Ground (s :==: l')))
      _                      -> empty
    notrace ("[mutate (left)] " <> show con) $
      return ("mutate (left) " <> show con, constraints <> [Ground (rhs :==: u)], MetaSubsts [])
  -- mutate (right)
  u :==: Con con args -> do
    Con con' args' :-> rhs <- choose rules >>= freshRule boundVars
    guard (con == con')
    guard (length args == length args')
    constraints <- flip traverse (zip args args') $ \case
      (Regular t, Regular l) -> pure (Ground (t :==: l))
      (Scoped s, Scoped l')  -> pure (Forall (Ground (s :==: l')))
      _                      -> empty
    notrace ("[mutate (right)] " <> show con) $
      return ("mutate (right) " <> show con, constraints <> [Ground (rhs :==: u)], MetaSubsts [])
  _ -> empty

-- | Mutate (meta) rule: \(\forall \overline{x_k}. m[\overline{t_k}] \stackrel{?}{=} u \longrightarrow \langle C_1 \cup C_2 \cup C_3, \mathsf{\sigma} \rangle \) where
--
-- * \(F(\overline{l_p}, \overline{x.l'_q}) \to r\) is in \(R\)
-- * \(\sigma = [m[\overline{z_n}] \mapsto F(\overline{m_p[\overline{z_k}]}, \overline{x.m'_q[x, \overline{z_k}]})] \)
-- * \( C_1 = \{ \forall \overline{x_k}. m_i[\overline{t_k}] \stackrel{?}{=} l_i \) for all \(i = 1 \ldots p \}\)
-- * \( C_2 = \{ \forall \overline{x_k}, x. m'_j[x, \overline{t_k}] \stackrel{?}{=} l'_j \) for all \(j = 1 \ldots m \}\)
-- * \( C_3 = \{ \forall \overline{x_k}. r \stackrel{?}{=} u \} \)
-- * \(m\) does not occur in \(u\)
mutateMeta
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => [Rule m Void]
  -> [Term m (IncMany a)]
  -> GroundConstraint m (IncMany a)
  -> f (String, [Constraint m (IncMany a)], MetaSubsts m (IncMany a))
mutateMeta rules boundVars = \case
  -- mutate meta (left)
  MetaVar m args :==: u
    | m `notElem` metavars u -> do
        rule@(Con con args' :-> rhs) <- choose rules >>= freshRule boundVars

        -- TODO: the heuristic below does not help, how can we cut the search space?
        -- let ruleConstructors = foldMap constructorsArg args'
        --    lhsConstructors = foldMap constructors args
        -- guard (any (`elem` lhsConstructors) ruleConstructors)

        (args'', constraints) <- runWriterT $
          traverse (argTermToMetaVar args . protect) args'
        notrace ("[mutate meta (left)] " <> ppRules [unsafeCoerce rule]) $
          return ("mutate meta (left) " <> ppRules [unsafeCoerce rule], constraints <> [Ground (rhs :==: u)],
            MetaSubsts [metaSubst m (length args) (Con con args'')])
  -- mutate meta (right)
--   u :==: MetaVar m args
--     | m `notElem` metavars u -> do
--         rule@(Con con args' :-> rhs) <- choose rules >>= freshRule boundVars
--         (args'', constraints) <- runWriterT $
--           traverse (argTermToMetaVar args) args'
--         notrace ("[mutate meta (right)] " <> ppRules [unsafeCoerce rule]) $
--           return (constraints <> [Ground (rhs :==: u)],
--             MetaSubsts [metaSubst m (length args) (Con con args'')])
  _ -> empty
  where
    protect :: ArgTerm m a -> ArgTerm m a
    protect (Regular t) = Regular (protect' t)
    protect (Scoped s)  = Scoped (protect' s)

    protect' :: Term m a -> Term m a
    protect' (Var x)          = Var x
    protect' (Con con args)   = Con (coerce (++ "'") con) (map protect args)
    protect' (MetaVar m args) = MetaVar m (map protect' args)

-- ** Helpers

-- | Check whether given list of terms is a list of distinct bound variables.
-- Return the function appropriate to use in substitution.
distinctBoundVars
  :: [Term m (IncMany a)]
  -> Maybe (IncMany a -> Term m (IncMany (IncMany a)))
distinctBoundVars xs
  | distinct  = Just mapping
  | otherwise = Nothing
  where
    indices = traverse toIndex xs
    Just indices' = indices

    toIndex (Var (B i)) = Just i
    toIndex _           = Nothing

    distinct =
      case indices of
        Just is -> nub is == is
        Nothing -> False

    mapping z@(B i) =
      case elemIndex i indices' of
        Nothing -> Var (F z)
        Just j  -> Var (B j)
    mapping z = Var (F z)

-- | Generate a fresh meta variable corresponding to an argument of a constructor.
--
-- Used in 'imitate' and 'mutateMeta' rules.
argTermToMetaVar
  :: MonadFresh m f
  => [Term m var]   -- ^ Parameters of the meta variable on the LHS of the 'imitate'/'mutateMeta' rule.
  -> ArgTerm m var  -- ^ Argument term of a constructor.
  -> WriterT [Constraint m var] f (ArgTerm m (IncMany var))
argTermToMetaVar args = \case
  Regular u -> do
    v <- fresh
    let constraint = Ground (MetaVar v args :==: u)
        newArgTerm = Regular (MetaVar v [ Var (B i) | i <- [0..n-1] ])
    tell [constraint]
    return newArgTerm
  Scoped s -> do
    v <- fresh
    let constraint = Forall (Ground (MetaVar v (Var Z : map (fmap S) args) :==: s))
        newArgTerm = Scoped (MetaVar v (Var Z : [ Var (S (B i)) | i <- [0..n-1] ]))
    tell [constraint]
    return newArgTerm
  where
    n = length args

-- | Generate a fresh version of a rewrite rule
-- given a list of additional parameters for the meta variables.
--
-- Used in 'mutate' and 'mutateMeta' rules.
freshRule :: (Eq m, MonadFresh m f) => [Term m a] -> Rule m Void -> f (Rule m a)
freshRule boundVars (lhs :-> rhs) = flip evalStateT [] $ do
  lhs' <- traverseMeta boundVars (vacuous lhs)
  rhs' <- traverseMeta boundVars (vacuous rhs)
  return (lhs' :-> rhs')
  where
    traverseMeta
      :: (Eq m, MonadFresh m f)
      => [Term m a]
      -> Term m a
      -> StateT [(m, m)] f (Term m a)
    traverseMeta bvars = \case
      Var x          -> pure (Var x)
      Con con args   -> Con con <$> traverse (traverseMetaArg bvars) args
      MetaVar m args -> do
        args' <- traverse (traverseMeta bvars) args
        mkFresh m bvars args'

    traverseMetaArg bvars = \case
      Regular t -> Regular <$> traverseMeta bvars t
      Scoped s  -> Scoped <$> traverseMeta (fmap S <$> bvars) s

    mkFresh :: (Eq m, MonadFresh m f) => m -> [Term m a] -> [Term m a] -> StateT [(m, m)] f (Term m a)
    mkFresh m bvars args = do
      m' <- gets (lookup m) >>= \case
        Nothing -> do
          m' <- lift fresh
          modify ((m, m') :)
          return m'
        Just m' -> return m'
      pure (MetaVar m' (args <> bvars))

-- * Helpers

-- | Non-deterministically select one element out of a list.
--
-- >>> selectOne [1..3] :: [(Int, [Int])]
-- [(1,[2,3]),(2,[1,3]),(3,[1,2])]
selectOne :: Alternative f => [a] -> f (a, [a])
selectOne = choose . splits

-- | All possible splits of a list into an element and a list of other elements.
--
-- >>> splits [1..3]
-- [(1,[2,3]),(2,[1,3]),(3,[1,2])]
splits :: [a] -> [(a, [a])]
splits xs =
  [ (x, before <> after)
  | (before, x:after) <- zip (inits xs) (tails xs) ]

-- | Choose a value from a list.
choose :: Alternative f => [a] -> f a
choose = foldr (<|>) empty . map pure

-- | Try the second computation only if the first one fails (i.e. no backtracking).
--
-- The following examples show the difference between 'orElse' and 'mplus' for 'Logic':
--
-- >>> observeAll (pure 1 `orElse` pure 2)
-- [1]
-- >>> observeAll (pure 1 `mplus` pure 2)
-- [1,2]
--
-- >>> observeAll $ do { x <- pure 1 `orElse` pure 2; guard (even x); return x }
-- []
-- >>> observeAll $ do { x <- pure 1 `mplus` pure 2; guard (even x); return x }
-- [2]
orElse :: MonadLogic m => m a -> m a -> m a
orElse mx my =
  msplit mx >>= \case
    Nothing      -> my
    Just (x, xs) -> pure x <|> xs

notrace :: String -> a -> a
notrace _ = id
-- notrace = trace

