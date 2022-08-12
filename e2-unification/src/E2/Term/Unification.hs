{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UndecidableInstances       #-}
module E2.Term.Unification where

-- import           Debug.Trace
import           Unsafe.Coerce

import           Control.Applicative
import           Control.Arrow         ((&&&))
import           Control.Monad
import           Control.Monad.Logic
import           Control.Monad.State
import           Control.Monad.Writer
import qualified Data.Bifunctor
import           Data.Functor.Identity
import           Data.List             (elemIndex, inits, intercalate, nub,
                                        tails)
import           Data.Semigroup
import           Data.Void

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

-- | A rule \(t \to u\).
data Rule metavar a
  = Term metavar a :-> Term metavar a
  deriving (Eq, Show)

-- | Extract rule's left hand side.
ruleLHS :: Rule m Void -> Term m Void
ruleLHS (lhs :-> _rhs) = lhs

-- | Extract left hand side from a collection of rules.
rulesLHS :: [Rule m Void] -> [Term m Void]
rulesLHS = map ruleLHS

-- | A ground constraint has no quantifiers.
data GroundConstraint metavar var
  = Term metavar var :==: Term metavar var  -- ^ \( t \stackrel{?}{=} u\)
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | A constraint is a ground constraint put under some number of quantifiers.
--
-- \(\forall \overline{x_k}. t \stackrel{?}{=} u\)
type Constraint metavar = Forall (GroundConstraint metavar)

-- | A meta variable substitution.
data MetaSubst m var = MetaSubst
  { metaSubstVar   :: m                     -- ^ Meta variable to be substituted.
  , metaSubstArity :: Int                   -- ^ Meta variable arity (for checks).
  , metaSubstBody  :: Term m (IncMany var)  -- ^ Meta variable body (a scoped term).
  } deriving (Show, Functor, Foldable, Traversable)

-- | Construct a meta variable substitution and
-- check that its declared arity is not exceeded in the body.
metaSubst :: m -> Int -> Term m (IncMany var) -> MetaSubst m var
metaSubst m arity body
  | actualArity >= Just (Max arity) = error "actual arity of the body exceeds declared arity of a meta variable"
  | otherwise = MetaSubst m arity body
  where
    actualArity = foldMap bound body
    bound (B i) = Just (Max i)
    bound (F _) = Nothing

-- | A collection of simultaneous meta variable substitutions.
newtype MetaSubsts m var = MetaSubsts
  { getMetaSubsts :: [MetaSubst m var] }
  deriving newtype (Show)
  deriving stock (Functor, Foldable, Traversable)

-- | Convert meta substitutions into a lookup list.
toLookupList :: MetaSubsts m var -> [(m, Term m (IncMany var))]
toLookupList = map (metaSubstVar &&& metaSubstBody) . getMetaSubsts

-- | Composition of substitutions.
instance Eq m => Semigroup (MetaSubsts m var) where
  MetaSubsts xs <> MetaSubsts ys = MetaSubsts (xs <> map update ys)
    where
      update ms@MetaSubst{..} = ms
        { metaSubstBody = substituteMeta' (`lookup` substs) metaSubstBody }

      substs = fmap (fmap (fmap F)) <$> toLookupList (MetaSubsts xs)

instance Eq m => Monoid (MetaSubsts m var) where
  mempty = MetaSubsts []

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
defaultUnify = head . flip evalFresh defaultVars . observeAllT . runUnify
  where
    defaultVars = [ Variable ("m" ++ toSub n) | n <- [0..] ]
    toSub = map toSubDigit . show
    mappings = zip "0123456789" "₀₁₂₃₄₅₆₇₈₉"
    toSubDigit d =
      case lookup d mappings of
        Nothing -> '.'
        Just c  -> c

-- * \(E^2\)-unification procedure

-- | Attempt applying one step of \(E^2\)-unification to a collection of constraints.
--
-- This will try to simplify constraints in the following way:
--
-- 0. If there are no constraints to simplify, then exit successfully.
-- 1. Apply 'delete' or 'eliminate' rule to some constraint if possible.
-- 2. Simplify any rigid-rigid constraint with 'decompose' or 'mutate' rules.
-- 3. Otherwise, apply 'project', 'imitate', or 'mutateMeta' rules.
tryE2
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [Rule m Void]    -- ^ Set \(R\) of rewrite rules.
  -> [Constraint m a] -- ^ Collection of constraints to simplify.
  -> f ([Constraint m a], MetaSubsts m a)
tryE2 _ [] = pure mempty
tryE2 rules constraints =
  -- apply delete and eliminate rules first (deterministic)
  once (tryDeleteEliminate constraints) `orElse`
    -- then solve rigid-rigid constraints (non-deterministic)
    tryRigidRigid constraints `orElse`
      -- finally, solve flex-rigid and flex-flex constraints
      tryFlex constraints
  where
    tryDeleteEliminate cs = do
      (c, cs') <- selectOne cs
      (cs'', substs) <- upgrade (\c' _bvars -> delete c' <|> eliminate c') c
      return (cs'' <> map (applySubsts substs) cs', substs)

    tryRigidRigid cs = do
      (c, cs') <- selectOne cs
      guard (isRigidRigid c)
      (cs'', substs) <- upgrade (\c' bvars -> decompose c' <|> mutate rules bvars c') c
      return (cs'' <> map (applySubsts substs) cs', substs)

    tryFlex cs = do
      (c, cs') <- selectOne cs
      (cs'', substs) <- upgrade (\c' bvars -> project c' <|> imitate c' <|> mutateMeta rules bvars c') c
      return (cs'' <> map (applySubsts substs) cs', substs)

    upgrade = convert . go []

    convert k c = do
      (cs, substs) <- k (fmap F c)
      cs' <- traverse (traverse removeIncMany) cs
      substs' <- traverse removeIncMany substs
      return (cs', substs')

--     go :: [Term m (IncMany a)]
--        -> (GroundConstraint m (IncMany a) -> [Term m (IncMany a)] -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a)))
--        -> Constraint m (IncMany a)
--        -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
    go bvars k (Ground c) = k c bvars
    go bvars k (Forall c) = do
      (cs, substs) <- go (Var (joinInc Z) : map (fmap (joinInc . S)) bvars) k (joinInc <$> c)
      cs' <- traverse (traverse decIncMany) cs
      substs' <- traverse decIncMany substs
      return (cs', substs')


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
    go depth [] = notrace ("solution found at depth = " <> show (depth - 1)) $
      return mempty
    go depth constraints
      | depth > maxDepth = pure (constraints, mempty)
      | otherwise = notrace (replicate (depth * 2) ' ' <> "[" <> show depth <> "] " <> ppConstraints' (unsafeCoerce constraints)) $ do
          (cs, substs) <- tryE2 rules constraints
          (cs', substs') <- go (depth + 1) cs
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
      | n > maxIterations = empty
      | otherwise = do
          tryClose (unifyDFS maxDepth rules constraints) >>= \case
            Left incompletes -> notrace (replicate (2 * n) ' ' <> "after iteration " <> show n <> " we have " <> show (length incompletes) <> " incomplete branches") $ do
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
      | null cs   -> pure (Right substs)
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

ppMetaSubsts' :: MetaSubsts Variable Variable -> String
ppMetaSubsts' = ppMetaSubsts defaultFreshVars getVariable

ppMetaSubsts :: [String] -> (a -> String) -> MetaSubsts Variable a -> String
ppMetaSubsts freshVars ppVar (MetaSubsts substs) =
  intercalate "\n" (map (ppMetaSubst freshVars ppVar) substs)

ppMetaSubst :: [String] -> (a -> String) -> MetaSubst Variable a -> String
ppMetaSubst freshVars ppVar (MetaSubst (Variable m) arity t)
  = case splitAt arity freshVars of
      (xs, ys)
        | length xs < arity -> error "not enough fresh variables"
        | otherwise ->
            let params = intercalate ", " xs
            in m <> "[" <> params <> "]" <> " -> " <> ppTerm ys (ppIncMany xs . fmap ppVar) t

ppRules :: [Rule Variable Void] -> String
ppRules = unlines . map ppRule
  where
    ppRule (t :-> t') = ppTerm defaultFreshVars absurd t <> " ——» " <> ppTerm defaultFreshVars absurd t'

-- * \(E^2\)-unification rules

-- | Delete rule: \(\forall \overline{x_k}. t \stackrel{?}{=} t \longrightarrow \langle \varnothing, \mathsf{id} \rangle \)
delete
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
delete = \case
  t :==: t'
    | t == t' -> notrace "[delete]" $ return ([], mempty)
  _ -> empty

-- | Decompose rule: \(\forall \overline{x_k}. F(\overline{t_n}, \overline{x.s_m}) \stackrel{?}{=} F(\overline{t'_n}, \overline{x.s'_m}) \longrightarrow \langle C_1 \cup C_2, \mathsf{id} \rangle \) where
--
-- * \( C_1 = \{ \forall \overline{x_k}. t_i \stackrel{?}{=} t'_i \) for all \(i = 1 \ldots n \}\)
-- * \( C_2 = \{ \forall \overline{x_k}, x. s_j \stackrel{?}{=} s'_j \) for all \(j = 1 \ldots m \}\)
decompose
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
decompose = \case
  Con con args :==: Con con' args'
    | con == con' && length args == length args' -> do
        args'' <- sequence $ zipWith mkConstraintArg args args'
        notrace ("[decompose] " <> show con) $ return (args'', mempty)
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
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
eliminate = \case
  -- eliminate (left)
  MetaVar m args :==: t
    | m `notElem` metavars t,
      Just zs <- distinctBoundVars args
      -> notrace "[eliminate (left)]" $ return ([], MetaSubsts [metaSubst m (length args) (t >>= zs)])
  -- eliminate (right)
  t :==: MetaVar m args
    | m `notElem` metavars t,
      Just zs <- distinctBoundVars args
      -> notrace "[eliminate (right)]" $ return ([], MetaSubsts [metaSubst m (length args) (t >>= zs)])
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
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
imitate = \case
  -- imitate (left)
  MetaVar m args :==: Con con args'
    | m `notElem` (foldMap metavarsArg args') -> do
      (args'', constraints) <- runWriterT $ traverse (argTermToMetaVar args) args'
      notrace ("[imitate (left)] " <> show con) $ return (constraints, MetaSubsts [metaSubst m (length args) (Con con args'')])
  -- imitate (right)
--   Con con args' :==: MetaVar m args
--     | m `notElem` (foldMap metavarsArg args') -> do
--       (args'', constraints) <- runWriterT $ traverse (argTermToMetaVar args) args'
--       notrace ("[imitate (right)] " <> show con) $ return (constraints, MetaSubsts [metaSubst m (length args) (Con con args'')])
  _ -> empty

-- | Project rule: \(\forall \overline{x_k}. m[\overline{t_k}] \stackrel{?}{=} u \longrightarrow \langle C, \sigma \rangle \) where
--
-- * \(\sigma = [m[\overline{z_n}] \mapsto z_i] \)
-- * \( C = \{ \forall \overline{x_k}. t_i \stackrel{?}{=} u \}\)
-- * \(m\) does not occur in \(u\)
project
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
project = \case
  -- project (left)
  MetaVar m args :==: u
    | m `notElem` metavars u -> do
      i <- choose [0 .. length args - 1]
      let constraint = Ground (args !! i :==: u)
      notrace "[project (left)]" $ return ([constraint], MetaSubsts [metaSubst m (length args) (Var (B i))])
  -- project (right)
--   MetaVar m args :==: u
--     | m `notElem` metavars u -> do
--       i <- choose [0 .. length args - 1]
--       let constraint = Ground (args !! i :==: u)
--       notrace "[project (right)]" $ return ([constraint], MetaSubsts [metaSubst m (length args) (Var (B i))])
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
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
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
      return (constraints <> [Ground (rhs :==: u)], MetaSubsts [])
  -- mutate (right)
--   u :==: Con con args -> do
--     Con con' args' :-> rhs <- choose rules >>= freshRule boundVars
--     guard (con == con')
--     guard (length args == length args')
--     constraints <- flip traverse (zip args args') $ \case
--       (Regular t, Regular l) -> pure (Ground (t :==: l))
--       (Scoped s, Scoped l')  -> pure (Forall (Ground (s :==: l')))
--       _                      -> empty
--     notrace ("[mutate (right)] " <> show con) $
--       return (constraints <> [Ground (rhs :==: u)], MetaSubsts [])
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
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
mutateMeta rules boundVars = \case
  -- mutate meta (left)
  MetaVar m args :==: u
    | m `notElem` metavars u -> do
        rule@(Con con args' :-> rhs) <- choose rules >>= freshRule boundVars
        (args'', constraints) <- runWriterT $
          traverse (argTermToMetaVar args) args'
        notrace ("[mutate meta (left)] " <> ppRules [unsafeCoerce rule]) $
          return (constraints <> [Ground (rhs :==: u)],
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

-- * Example TRS

-- ** Lambda calculus with pairs

-- | Rewrite rules for lambda calculus with pairs.
rulesLambda :: [Rule Variable Void]
rulesLambda =
  [ app (lam (MetaVar "m1" [Var Z])) (MetaVar "m2" [])
      :-> MetaVar "m1" [MetaVar "m2" []]
  , first (pair (MetaVar "m1" []) (MetaVar "m2" []))
      :-> MetaVar "m1" []
  , second (pair (MetaVar "m1" []) (MetaVar "m2" []))
      :-> MetaVar "m2" []
  ]

-- | A helper to create application terms \(t_1\;t_2\)
app :: Term Variable a -> Term Variable a -> Term Variable a
app f x = Con "APP" [Regular f, Regular x]

-- | A helper to create lambda abstraction terms \(\lambda x. t\)
lam :: Term Variable (Inc a) -> Term Variable a
lam body = Con "LAM" [Scoped body]

-- | A helper to create first project terms \(\pi_1\;t\)
first :: Term Variable a -> Term Variable a
first p = Con "FIRST" [Regular p]

-- | A helper to create second project terms \(\pi_2\;t\)
second :: Term Variable a -> Term Variable a
second p = Con "SECOND" [Regular p]

-- | A helper to create pair terms \(\langle t_1, t_2 \rangle\)
pair :: Term Variable a -> Term Variable a -> Term Variable a
pair f s = Con "PAIR" [Regular f, Regular s]

-- * Example terms and constraints

-- |
-- >>> putStrLn $ ppTerm' ex1
-- APP(LAM(x₁.m1[x₁]), m2[])
ex1 :: Term Variable a
ex1 = Con "APP" [ Regular (Con "LAM" [ Scoped (MetaVar "m1" [Var Z]) ]), Regular (MetaVar "m2" []) ]

-- |
-- >>> putStrLn $ ppTerm' ex2
-- m1[m2[]]
ex2 :: Term Variable a
ex2 = MetaVar "m1" [MetaVar "m2" []]

-- |
-- >>> putStrLn $ ppTerm' ex3
-- APP(m[], x)
ex3 :: Term'
ex3 = Con "APP" [ Regular (MetaVar "m" []), Regular (Var "x") ]

-- |
-- >>> putStrLn $ ppConstraint' ex4
-- APP(m[y], x) =?= y
ex4 :: Constraint Variable Variable
ex4 = Ground (app (MetaVar "m" [Var "y"]) (Var "x") :==: Var "y")

-- |
-- >>> putStrLn $ ppConstraint' ex5
-- forall x₁.forall x₂.m1[x₂, x₁] =?= APP(x₁, x₂)
--
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 5 rulesLambda [ ex5 ]
-- m1[x₁, x₂] -> APP(x₂, x₁)
ex5 :: Constraint Variable Variable
ex5 = Forall $ Forall $
  Ground (MetaVar "m1" [Var Z, Var (S Z)]
    :==: Con "APP" [Regular (Var (S Z)), Regular (Var Z)] )

-- |
-- >>> putStrLn $ ppConstraint' ex6
-- APP(m[], PAIR(LAM(x₁.APP(x₁, y)), g)) =?= APP(g, y)
--
-- FIXME: unification does not finish in reasonable time!
ex6 :: Constraint Variable Variable
ex6 = Ground (app (MetaVar "m" []) (Con "PAIR" [Regular (lam (app (Var Z) (Var (S "y")))), Regular (Var "g")]) :==: app (Var "g") (Var "y"))

-- |
-- >>> putStrLn $ ppConstraint' ex7
-- m[y, g] =?= APP(g, y)
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 5 rulesLambda [ ex7 ]
-- m[x₁, x₂] -> APP(x₂, x₁)
ex7 :: Constraint Variable Variable
ex7 = Ground (MetaVar "m" [Var "y", Var "g"] :==: app (Var "g") (Var "y"))

-- |
-- >>> putStrLn $ ppConstraint' ex8
-- APP(m[y], g) =?= APP(g, y)
--
-- FIXME: takes too long
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 4 rulesLambda [ ex8 ]
-- m[x₁] -> LAM(x₂.APP(x₂, x₁))
ex8 :: Constraint Variable Variable
ex8 = Ground (app (MetaVar "m" [Var "y"]) (Var "g") :==: app (Var "g") (Var "y"))

-- |
-- >>> putStrLn $ ppConstraint' ex9
-- m[PAIR(y, g)] =?= g
--
-- FIXME: takes a bit too long and contains unresolved metavariable!
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 4 rulesLambda [ ex9 ]
-- m[x₁] -> APP(LAM(x₂.SECOND(x₁)), m₉[x₁])
--
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 5 rulesLambda [ ex9 ]
-- m[x₁] -> SECOND(x₁)
ex9 :: Constraint Variable Variable
ex9 = Ground (MetaVar "m" [pair (Var "y") (Var "g")] :==: Var "g")

-- * Fresh name supply monad

-- | A monad transformer with fresh name supply.
newtype FreshT v m a = FreshT { runFreshT :: StateT [v] m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFail)

-- | Evaluate a computation with given supply of fresh names.
evalFreshT :: Monad m => FreshT v m a -> [v] -> m a
evalFreshT (FreshT m) vars = evalStateT m vars

-- | Simple fresh name supply context.
type Fresh v = FreshT v Identity

-- | Evaluate a computation with given supply of fresh names.
evalFresh :: Fresh v a -> [v] -> a
evalFresh m = runIdentity . evalFreshT m

-- | A monad that is capable of generating fresh names of type 'v'.
class Monad m => MonadFresh v m | m -> v where
  -- | Generate a fresh name.
  fresh :: m v

instance (Monoid w, MonadFresh v m) => MonadFresh v (WriterT w m) where
  fresh = lift fresh

instance Monad m => MonadFresh v (FreshT v m) where
  fresh = FreshT $ do
    get >>= \case
      [] -> error "not enough fresh variables"
      v:vs -> do
        put vs
        notrace ("issuing fresh meta " <> unsafeCoerce v) $ return v

instance MonadPlus m => Alternative (FreshT v m) where
  empty = FreshT $ lift empty
  FreshT slx <|> FreshT sly = FreshT $ do
    vars <- get
    (result, vars') <- lift $ runStateT slx vars <|> runStateT sly vars
    put vars'
    return result

instance MonadPlus m => MonadPlus (FreshT v m) where
  mzero = empty
  mplus = (<|>)

-- FIXME: invalid instance! it is probably impossible to make it correct
-- instance (MonadPlus m, MonadLogic m) => MonadLogic (FreshT v m) where
--   msplit (FreshT m) = FreshT $ do
--     vars <- get
--     lift (msplit (runStateT m vars)) >>= \case
--       Nothing      -> return Nothing
--       Just ((x, vars'), xs) -> do
--         put vars'
--         return $ Just $ (,) x $ FreshT $ do
--           (y, vars'') <- lift xs
--           put vars''
--           return y

instance MonadFresh v m => MonadFresh v (LogicT m) where
  fresh = lift fresh

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

