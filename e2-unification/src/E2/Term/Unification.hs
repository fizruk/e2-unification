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

import           Debug.Trace
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
                                        tails, transpose)
import           Data.Maybe            (catMaybes, fromMaybe)
import           Data.Semigroup
import           Data.Void

import           E2.Term

notrace :: String -> a -> a
notrace _ = id
-- notrace = trace

data Forall t var
  = Forall (Forall t (Inc var))
  | Ground (t var)

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

data Rule metavar a
  = Term metavar a :-> Term metavar a
  deriving (Eq, Show)

ruleLHS :: Rule m Void -> Term m Void
ruleLHS (lhs :-> _rhs) = lhs

rulesLHS :: [Rule m Void] -> [Term m Void]
rulesLHS = map ruleLHS

data GroundConstraint metavar var
  = Term metavar var :==: Term metavar var
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Constraint metavar = Forall (GroundConstraint metavar)

data MetaSubst m var = MetaSubst
  { metaSubstVar   :: m
  , metaSubstArity :: Int
  , metaSubstBody  :: Term m (IncMany var)
  } deriving (Show, Functor, Foldable, Traversable)

metaSubst :: m -> Int -> Term m (IncMany var) -> MetaSubst m var
metaSubst m arity body
  | actualArity >= Just (Max arity) = error "actual arity of the body exceeds declared arity of a meta variable"
  | otherwise = MetaSubst m arity body
  where
    actualArity = foldMap bound body
    bound (B i) = Just (Max i)
    bound (F _) = Nothing

newtype MetaSubsts m var = MetaSubsts
  { getMetaSubsts :: [MetaSubst m var] }
  deriving newtype (Show)
  deriving stock (Functor, Foldable, Traversable)

toLookupList :: MetaSubsts m var -> [(m, Term m (IncMany var))]
toLookupList = map (metaSubstVar &&& metaSubstBody) . getMetaSubsts

instance Eq m => Semigroup (MetaSubsts m var) where
  MetaSubsts xs <> MetaSubsts ys = MetaSubsts (xs <> map update ys)
    where
      update ms@MetaSubst{..} = ms
        { metaSubstBody = substituteMeta' (`lookup` substs) metaSubstBody }

      substs = fmap (fmap (fmap F)) <$> toLookupList (MetaSubsts xs)

instance Eq m => Monoid (MetaSubsts m var) where
  mempty = MetaSubsts []

applySubsts :: Eq m => MetaSubsts m a -> Constraint m a -> Constraint m a
applySubsts substs = \case
  Forall c          -> Forall (applySubsts (S <$> substs) c)
  Ground (t :==: s) -> Ground (f t :==: f s)
  where
    f = substituteMeta' $ \m ->
          case lookup m (toLookupList substs) of
            Nothing -> Nothing
            Just t' -> Just t'

newtype Unify v a = Unify { runUnify :: LogicT (Fresh v) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadFail, MonadFresh v, MonadLogic)

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

newtype FreshT v m a = FreshT { runFreshT :: StateT [v] m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFail)

type Fresh v = FreshT v Identity

evalFreshT :: Monad m => FreshT v m a -> [v] -> m a
evalFreshT (FreshT m) vars = evalStateT m vars

evalFresh :: Fresh v a -> [v] -> a
evalFresh m = runIdentity . evalFreshT m

class Monad m => MonadFresh v m | m -> v where
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

e2
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [Rule m Void]
  -> [ GroundConstraint m (IncMany a)
       -> [Term m (IncMany a)]
       -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))]
e2 rules =
  [ \c _bvars -> delete c <|> eliminate c
  , \c bvars -> decompose c <|> mutate rules bvars c
  , \c bvars -> project c <|> imitate c <|> mutateMeta rules bvars c
  ]

e2'
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [Rule m Void]
  -> [ Constraint m a -> f ([Constraint m a], MetaSubsts m a) ]
e2' = map (convert . go []) . e2
  where
--     convert
--       :: (Constraint m (IncMany a) -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a)))
--       -> Constraint m a
--       -> f ([Constraint m a], MetaSubsts m a)
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

tryE2
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [Rule m Void]
  -> [Constraint m a]
  -> f ([Constraint m a], MetaSubsts m a)
tryE2 _ [] = pure mempty
tryE2 rules cs =
  once (tryDeleteEliminate cs) `orElse`   -- apply delete and eliminate rules first (deterministic)
    tryRigidRigid cs `orElse`             -- then solve rigid-rigid constraints (non-deterministic)
      tryFlex cs                          -- finally, solve flex-rigid and flex-flex constraints
  where
    tryDeleteEliminate cs = do
      (c, cs') <- selectOne cs
      (cs'', substs) <- upgrade (\c _bvars -> delete c <|> eliminate c) c
      return (cs'' <> map (applySubsts substs) cs', substs)

    tryRigidRigid cs = do
      (c, cs') <- selectOne cs
      guard (isRigidRigid c)
      (cs'', substs) <- upgrade (\c bvars -> decompose c <|> mutate rules bvars c) c
      return (cs'' <> map (applySubsts substs) cs', substs)

    tryFlex cs = do
      (c, cs') <- selectOne cs
      (cs'', substs) <- upgrade (\c bvars -> project c <|> imitate c <|> mutateMeta rules bvars c) c
      return (cs'' <> map (applySubsts substs) cs', substs)

--     go [] = empty
--     go (f:fs) = do
--       let (rigids, flexes) = partition isRigidRigid cs
--       -- FIXME: is it correct to always demand reduction of rigid-rigid constraints first? (I think it is, but I'm not sure; it does speed up the search significantly though)
--       msplit ((once (fmap (<> flexes) <$> selectOne rigids) `orElse` selectOne flexes) >>= \(c, cs') -> do
--         (cs'', substs) <- f c
--         return (cs'' <> map (applySubsts substs) cs', substs)) >>= \case
--           Nothing      -> go fs
--           Just (x, xs) -> pure x <|> xs

--     convert
--       :: (Constraint m (IncMany a) -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a)))
--       -> Constraint m a
--       -> f ([Constraint m a], MetaSubsts m a)
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


isRigidRigid :: Constraint m a -> Bool
isRigidRigid (Forall c)                  = isRigidRigid c
isRigidRigid (Ground (MetaVar{} :==: _)) = False
isRigidRigid (Ground (_ :==: MetaVar{})) = False
isRigidRigid (Ground _)                  = True

unifyDFS
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => Int
  -> [Rule m Void]
  -> [Constraint m a]
  -> f ([Constraint m a], MetaSubsts m a)
unifyDFS maxDepth rules = go 0
  where
    go depth [] = trace ("solution found at depth = " <> show (depth - 1)) $
      return mempty
    go depth constraints
      | depth > maxDepth = pure (constraints, mempty)
      | otherwise = trace (replicate (depth * 2) ' ' <> "[" <> show depth <> "] " <> ppConstraints' (unsafeCoerce constraints)) $ do
          (cs, substs) <- tryE2 rules constraints
          (cs', substs') <- go (depth + 1) cs
          return (cs', substs' <> substs)

unifyBFSviaDFS
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => Int  -- ^ Number of DFS interations.
  -> Int  -- ^ Max depth per one DFS iteration.
  -> [Rule m Void]
  -> [Constraint m a]
  -> f (MetaSubsts m a)
unifyBFSviaDFS maxIterations maxDepth rules = fmap . clean <*> go 0
  where
    go n [] = trace ("solution found at depth = " <> show n) $
      pure mempty
    go n constraints
      | n > maxIterations = empty
      | otherwise = do
          tryClose (unifyDFS maxDepth rules constraints) >>= \case
            Left incompletes -> trace (replicate (2 * n) ' ' <> "after iteration " <> show n <> " we have " <> show (length incompletes) <> " incomplete branches") $ do
              (cs, substs) <- choose incompletes
              substs' <- go (n + 1) cs
              return (substs' <> substs)
            Right substs -> trace ("solution found on iteration = " <> show (n + 1)) $
              pure substs

    -- leave only substitutions for metavariables that occur in the original constraints
    clean constraints (MetaSubsts substs) = MetaSubsts (filter isOriginalMeta substs)
      where
        metas = foldMap constraintMetaVars constraints
        isOriginalMeta MetaSubst{..} = metaSubstVar `elem` metas

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

constraintMetaVars :: Constraint m a -> [m]
constraintMetaVars (Forall c)           = constraintMetaVars c
constraintMetaVars (Ground (t :==: t')) = metavars t <> metavars t'

unify
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [Rule m Void]
  -> [Constraint m a]
  -> f (MetaSubsts m a)
unify _ [] = return mempty
unify rules cs = do
  tryRulePrec (e2 rules) cs >>- \ (cs', substs) -> do
    substs' <- unify rules cs'
    return (substs' <> substs)

unify'
  :: Int
  -> [Rule Variable Void]
  -> [Constraint Variable Variable]
  -> Unify Variable (MetaSubsts Variable Variable)
unify' maxDepth = go 0
  where
    go _ _ [] = return mempty
    go n _ _ | n > maxDepth = empty
    go n rules constraints = notrace ("[" <> show n <> "] " <> (ppConstraints' constraints)) $ do
      tryAsLastStep (oneStep rules constraints) <|> (oneStep rules constraints
        >>- \ (cs', substs) -> do
            substs' <- go (n + 1) rules cs'
            return (substs' <> substs))

    tryAsLastStep
      :: Unify Variable ([Constraint Variable Variable], MetaSubsts Variable Variable)
      -> Unify Variable (MetaSubsts Variable Variable)
    tryAsLastStep m = do
      msplit m >>= \case
        Nothing -> empty
        Just ((cs, substs), xs)
          | null cs -> pure substs
          | otherwise -> tryAsLastStep xs

    oneStep rules = tryRulePrec (e2 rules)


selectOne :: Alternative f => [a] -> f (a, [a])
selectOne = choose . splits

splits :: [a] -> [(a, [a])]
splits xs =
  [ (x, before <> after)
  | (before, x:after) <- zip (inits xs) (tails xs) ]

tryRulePrec
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [GroundConstraint m (IncMany a) -> [Term m (IncMany a)] -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))]
  -> [Constraint m a]
  -> f ([Constraint m a], MetaSubsts m a)
tryRulePrec [] _ = empty
tryRulePrec rules constraints = do
  outcomes <- flip traverse (splits constraints) $ \(c, cs) -> do
    outcomes <- flip traverse rules $ \rule -> do
      msplit (tryRule' [rule] c) >>= \case
        Nothing      -> pure Nothing
        Just (x, xs) -> pure $ Just $ do
          (cs', substs) <- reflect (Just (x, xs))
          return (cs' <> map (applySubsts substs) cs, substs)
    case catMaybes outcomes of
      [] -> pure Nothing
      _  -> pure (Just (map (fromMaybe empty) outcomes))
  case sequenceA outcomes of
    Nothing -> notrace "[DEAD END, backtracking]" empty
    Just outcomes' ->
      chooseFirst (transpose outcomes') -- >>= choose >>= id

chooseFirst :: MonadLogic f => [[f a]] -> f a
chooseFirst [] = empty
chooseFirst (xs:xss) =
  msplit (choose xs >>= id) >>= \case
    Nothing        -> chooseFirst xss
    Just (x, more) -> pure x <|> more

  {-
tryRulePrec [rules] (c:cs) =
  (tryRule' [rules] c >>- \(cs', substs) -> return (cs' <> map (applySubsts substs) cs, substs) )
  <|> trace "[DEAD END, backtracking]" empty
tryRulePrec (rules:ruleGroups) constraints =
  tryFirstRules <|> tryRulePrec ruleGroups constraints
  where
    tryFirstRules = do
      selectOne constraints >>- \(c, cs) ->
        tryRule' [rules] c >>- \(cs', substs) ->
          return (cs' <> map (applySubsts substs) cs, substs)
          -}

tryRule'
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [GroundConstraint m (IncMany a) -> [Term m (IncMany a)] -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))]
  -> Constraint m a
  -> f ([Constraint m a], MetaSubsts m a)
tryRule' rules constraint = do
  (cs, substs) <- tryRule rules [] (fmap F constraint)
  cs' <- traverse removeAllIncMany cs
  substs' <- removeAllIncMany substs
  return (cs', substs')

tryRule
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f, MonadLogic f)
  => [GroundConstraint m (IncMany a) -> [Term m (IncMany a)] -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))]
  -> [Term m (IncMany a)] -- bound vars    FIXME: handle better
  -> Constraint m (IncMany a)
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
tryRule rules bvars = \case

  Forall c -> do
    (cs, substs) <- tryRule rules (Var (joinInc Z) : map (fmap (joinInc . S)) bvars) (joinInc <$> c)

    -- FIXME: handle leftover bound variables better?
    cs'     <- traverse (traverse decIncMany) cs
    substs' <- traverse decIncMany substs

    return (cs', substs')

  Ground c -> do
    rule <- choose rules
    rule c bvars

--
--
--   -- mutate
--   Ground (Con con args :==: t) -> do
--     Con con' args' :-> rhs <- choose rules >>= freshRule
--     guard (con == con')
--     guard (length args == length args')
--     constraints <- sequence $ zipWith mkConstraintArg (vacuous <$> args') args
--     return (Ground (t :==: vacuous rhs) : constraints, mempty)
--
--   -- imitate
--   Ground (t@(Con (Label con) args) :==: MetaVar m args')
--     | m `notElem` metavars t -> do
--         let n = length args
--         let makeFreshArgs = mapM argTermToMetaVar args
--         freshArgsBound <- map (Var . B) [0..n - 1] <$> makeFreshArgs
--         freshArgs' <- makeFreshArgs >>= fmap ($ args')
--         let subst = (m, Con (Label ("!" <> con)) (map ($ fmap (Var . B) [0..n - 1]) freshArgsBound))
--         let constraints = zipWith (\l r -> Ground (l :==: r)) freshArgs' args
--         return (constraints, [subst])
--         _
--   Ground (MetaVar m args :==: t)
--     | m `notElem` metavars t -> do
--         Con con args <- choose (rulesLHS rules)
--         _
--
--   Ground (MetaVar{} :==: MetaVar{}) -> empty

distinctBoundVars :: [Term m (IncMany a)] -> Maybe (IncMany a -> Term m (IncMany (IncMany a)))
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

argTermToMetaVar
  :: MonadFresh m f
  => [Term m var]
  -> ArgTerm m var
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

choose :: Alternative f => [a] -> f a
choose = foldr (<|>) empty . map pure

rulesLambda :: [Rule Variable Void]
rulesLambda =
  [ app (lam (MetaVar "m1" [Var Z])) (MetaVar "m2" [])
      :-> MetaVar "m1" [MetaVar "m2" []]
  , first (pair (MetaVar "m1" []) (MetaVar "m2" []))
      :-> MetaVar "m1" []
  , second (pair (MetaVar "m1" []) (MetaVar "m2" []))
      :-> MetaVar "m2" []
  ]

app :: Term Variable a -> Term Variable a -> Term Variable a
app f x = Con "APP" [Regular f, Regular x]

lam :: Term Variable (Inc a) -> Term Variable a
lam body = Con "LAM" [Scoped body]

first :: Term Variable a -> Term Variable a
first p = Con "FIRST" [Regular p]

second :: Term Variable a -> Term Variable a
second p = Con "SECOND" [Regular p]

pair :: Term Variable a -> Term Variable a -> Term Variable a
pair f s = Con "PAIR" [Regular f, Regular s]

-- match :: Term m1 Void -> Term m2 var -> Maybe (MetaSubsts m1 m2 var)
-- match t1 t2 = match' (vacuous t1) (F <$> t2)
--
-- match'
--   :: Term m1 (IncMany Void)
--   -> Term m2 (IncMany var)
--   -> Maybe (MetaSubsts m1 m2 var)
-- match' pat term =
--   case (pat, term) of
--     (Var (F x), _) -> absurd x
--     (Var (B x), Var (B x')) -> do
--       guard (x == x')
--       return (MetaSubsts [])
--
--     (Con con pats, Con con' args)
--       | con /= con' -> Nothing
--       | length pats /= length args -> Nothing
--       | otherwise -> mconcat <$> sequence (zipWith matchArg pats args)
--
--     (MetaVar m pats, t) -> do
--       vars <- distinctBoundVars pats
--       t' <- traverse (toIncMany vars) t
--       return (MetaSubsts [(m, t')])
--
--     (_, _) -> Nothing
--   where
--     toIncMany _ (F x) = Just (F x)
--     toIncMany vars (B x) =
--       case findIndex (== x) vars of
--         Nothing -> Nothing
--         Just i  -> Just (B i)
--
-- distinctBoundVars :: MonadPlus f => [Term m (IncMany a)] -> f [Int]
-- distinctBoundVars ts = do
--   vars <- forM ts $ \case
--     Var (B x) -> return x
--     _         -> mzero
--   guard (length vars == length (nub vars))
--   return vars
--
-- matchArg
--   :: ArgTerm m1 (IncMany Void)
--   -> ArgTerm m2 (IncMany var)
--   -> Maybe (MetaSubsts m1 m2 var)
-- matchArg pat term =
--   case (pat, term) of
--     (Regular t, Regular t') -> match' t t'
--     (Scoped s, Scoped s')   -> match' (joinInc <$> s) (joinInc <$> s')
--     _                       -> Nothing


ex1 :: Term Variable Void
ex1 = Con "APP" [ Regular (Con "LAM" [ Scoped (MetaVar "m1" [Var Z]) ]), Regular (MetaVar "m2" []) ]

ex2 :: Term Variable Void
ex2 = MetaVar "m1" [MetaVar "m2" []]

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
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unify' rulesLambda [ ex5 ]
-- m1[x₁, x₂] -> APP(x₂, x₁)
ex5 :: Constraint Variable Variable
ex5 = Forall $ Forall $
  Ground (MetaVar "m1" [Var Z, Var (S Z)]
    :==: Con "APP" [Regular (Var (S Z)), Regular (Var Z)] )

ex6 :: Constraint Variable Variable
ex6 = Ground (app (MetaVar "m" []) (Con "PAIR" [Regular (lam (app (Var Z) (Var (S "y")))), Regular (Var "g")]) :==: app (Var "g") (Var "y"))

ex7 :: Constraint Variable Variable
ex7 = Ground (MetaVar "m" [Var "y", Var "g"] :==: app (Var "g") (Var "y"))

ex8 :: Constraint Variable Variable
ex8 = Ground (app (MetaVar "m" [Var "y"]) (Var "g") :==: app (Var "g") (Var "y"))

ex9 :: Constraint Variable Variable
ex9 = Ground (MetaVar "m" [pair (Var "y") (Var "g")] :==: Var "g")

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
  unlines (map (ppMetaSubst freshVars ppVar) substs)

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

delete
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
delete = \case
  t :==: t'
    | t == t' -> trace "[delete]" $ return ([], mempty)
  _ -> empty

decompose
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
decompose = \case
  Con con args :==: Con con' args'
    | con == con' && length args == length args' -> do
        args'' <- sequence $ zipWith mkConstraintArg args args'
        trace ("[decompose] " <> show con) $ return (args'', mempty)
  _ -> empty
  where
    mkConstraintArg (Regular t) (Regular t') = return $ Ground (t :==: t')
    mkConstraintArg (Scoped s) (Scoped s')   = return $ Forall $ Ground (s :==: s')
    mkConstraintArg _ _ = mzero

eliminate
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
eliminate = \case
  -- eliminate (left)
  MetaVar m args :==: t
    | m `notElem` metavars t,
      Just zs <- distinctBoundVars args
      -> trace "[eliminate (left)]" $ return ([], MetaSubsts [metaSubst m (length args) (t >>= zs)])
  -- eliminate (right)
  t :==: MetaVar m args
    | m `notElem` metavars t,
      Just zs <- distinctBoundVars args
      -> trace "[eliminate (right)]" $ return ([], MetaSubsts [metaSubst m (length args) (t >>= zs)])
  _ -> empty

imitate
  :: (Eq m, Eq a, MonadPlus f, MonadFail f, MonadFresh m f)
  => GroundConstraint m (IncMany a)
  -> f ([Constraint m (IncMany a)], MetaSubsts m (IncMany a))
imitate = \case
  -- imitate (left)
  MetaVar m args :==: Con con args'
    | m `notElem` (foldMap metavarsArg args') -> do
      (args'', constraints) <- runWriterT $ traverse (argTermToMetaVar args) args'
      trace ("[imitate (left)] " <> show con) $ return (constraints, MetaSubsts [metaSubst m (length args) (Con con args'')])
  -- imitate (right)
--   Con con args' :==: MetaVar m args
--     | m `notElem` (foldMap metavarsArg args') -> do
--       (args'', constraints) <- runWriterT $ traverse (argTermToMetaVar args) args'
--       trace ("[imitate (right)] " <> show con) $ return (constraints, MetaSubsts [metaSubst m (length args) (Con con args'')])
  _ -> empty

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
      trace "[project (left)]" $ return ([constraint], MetaSubsts [metaSubst m (length args) (Var (B i))])
  -- project (right)
--   MetaVar m args :==: u
--     | m `notElem` metavars u -> do
--       i <- choose [0 .. length args - 1]
--       let constraint = Ground (args !! i :==: u)
--       trace "[project (right)]" $ return ([constraint], MetaSubsts [metaSubst m (length args) (Var (B i))])
  _ -> empty

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
    trace ("[mutate (left)] " <> show con) $
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
--     trace ("[mutate (right)] " <> show con) $
--       return (constraints <> [Ground (rhs :==: u)], MetaSubsts [])
  _ -> empty

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
        trace ("[mutate meta (left)] " <> ppRules [unsafeCoerce rule]) $
          return (constraints <> [Ground (rhs :==: u)],
            MetaSubsts [metaSubst m (length args) (Con con args'')])
  -- mutate meta (right)
--   u :==: MetaVar m args
--     | m `notElem` metavars u -> do
--         rule@(Con con args' :-> rhs) <- choose rules >>= freshRule boundVars
--         (args'', constraints) <- runWriterT $
--           traverse (argTermToMetaVar args) args'
--         trace ("[mutate meta (right)] " <> ppRules [unsafeCoerce rule]) $
--           return (constraints <> [Ground (rhs :==: u)],
--             MetaSubsts [metaSubst m (length args) (Con con args'')])
  _ -> empty

-- * Helpers

orElse :: MonadLogic m => m a -> m a -> m a
orElse mx my =
  msplit mx >>= \case
    Nothing      -> my
    Just (x, xs) -> pure x <|> xs
