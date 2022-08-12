{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
module E2.Term where

import           Unsafe.Coerce

import           Control.Monad (ap)
import           Data.Char     (chr, ord)
import           Data.List     (intercalate)
import           Data.String   (IsString (..))

-- $setup
-- >>> :set -XOverloadedStrings

-- | A variable token, identified by its name.
newtype Variable = Variable { getVariable :: String }
  deriving newtype (Eq, Show, IsString)

-- | A label (such as constructor label).
newtype Label = Label { getLabel :: String }
  deriving newtype (Eq, Show, IsString)

-- | A term, parametrised by the type of its metavariables and variables.
data Term metavar var
  = Var var
  -- ^ A variable term.
  | Con Label [ArgTerm metavar var]
  -- ^ A constructor (a.k.a. function symbol), fully applied to all its arguments.
  | MetaVar metavar [Term metavar var]
  -- ^ A parametrised metavariable.
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Extract a list of all metavariable names that occur in a given term.
metavars :: Term m a -> [m]
metavars = \case
  Var{}          -> []
  Con _ args     -> foldMap metavarsArg args
  MetaVar m args -> m : foldMap metavars args

-- | Extract a list of all metavariable names that occur in a given argment term.
metavarsArg :: ArgTerm m a -> [m]
metavarsArg = \case
  Regular t -> metavars t
  Scoped  s -> metavars s

instance Applicative (Term metavar) where
  pure = return
  (<*>) = ap

instance Monad (Term metavar) where
  return = Var
  Var x           >>= f = f x
  Con con args    >>= f = Con con (map k args)
    where
      k (Regular t) = Regular (t >>= f)
      k (Scoped s) = Scoped (s >>= f')
        where
          f' Z     = return Z
          f' (S x) = S <$> f x
  MetaVar m args  >>= f = MetaVar m (map (>>= f) args)

-- | A convenient version of 'Term'.
type Term' = Term Variable Variable

-- | Pretty print a 'Term''.
--
-- >>> t = Con "APP" [Regular (Con "LAM" [Scoped (MetaVar "m1" [Var Z])]), Regular (MetaVar "m2" [])]
-- >>> putStrLn $ ppTerm' t
-- APP(LAM(x₁.m1[x₁]), m2[])
ppTerm' :: Term' -> String
ppTerm' = ppTerm defaultFreshVars getVariable

-- | Pretty print a 'Term'.
ppTerm :: [String] -> (a -> String) -> Term Variable a -> String
ppTerm freshVars ppVar = \case
  Var x -> ppVar x
  Con (Label con) args -> con <> "(" <> intercalate ", " (map (ppArgTerm freshVars ppVar) args) <> ")"
  MetaVar (Variable m) args -> m <> "[" <> intercalate ", " (map (ppTerm freshVars ppVar) args) <> "]"

-- | Pretty print an argument term (regular or scoped).
ppArgTerm
  :: [String]             -- ^ A (possibly infinite) list of fresh names for bound variables.
  -> (a -> String)        -- ^ A pretty printing function for free variables.
  -> ArgTerm Variable a   -- ^ An argument term.
  -> String
ppArgTerm freshVars ppVar = \case
  Regular t -> ppTerm freshVars ppVar t
  Scoped s  ->
    case freshVars of
      []   -> error "not enough fresh variables"
      x:xs -> x <> "." <> ppTerm xs (ppInc x . fmap ppVar) s

ppInc :: String -> Inc String -> String
ppInc def Z   = def
ppInc _ (S x) = x

ppIncMany :: [String] -> IncMany String -> String
ppIncMany xs (B i) = (xs !!? "ppIncMany") i
ppIncMany _ (F x)  = x

data Inc var = Z | S var
  deriving (Eq, Show, Functor, Foldable, Traversable)

data IncMany var = B Int | F var
  deriving (Eq, Show, Functor, Foldable, Traversable)

instantiateMany :: Monad f => (Int -> f a) -> f (IncMany a) -> f a
instantiateMany f t = t >>= \case
  B i -> f i
  F x -> return x

data ArgTerm metavar var
  = Regular (Term metavar var)
  | Scoped  (Term metavar (Inc var))
  deriving (Eq, Show, Functor, Foldable, Traversable)

type ArgTerm' = ArgTerm Variable

substitute :: (a -> Term m b) -> Term m a -> Term m b
substitute f = \case
  Var x          -> f x
  Con con args   -> Con con (substituteArg f <$> args)
  MetaVar m args -> MetaVar m (substitute f <$> args)

substituteArg :: (a -> Term m b) -> ArgTerm m a -> ArgTerm m b
substituteArg f = \case
  Regular t -> Regular (substitute f t)
  Scoped s  -> Scoped (substitute f' s)
  where
    f' Z     = Var Z
    f' (S x) = S <$> f x

renameMeta :: (m -> n) -> Term m a -> Term n a
renameMeta f = \case
  Var x          -> Var x
  Con con args   -> Con con (renameMetaArg f <$> args)
  MetaVar m args -> MetaVar (f m) (renameMeta f <$> args)

renameMetaArg :: (m -> n) -> ArgTerm m a -> ArgTerm n a
renameMetaArg f = \case
  Regular t -> Regular (renameMeta f t)
  Scoped s  -> Scoped (renameMeta f s)

substituteMeta :: (m -> Term n (IncMany a)) -> Term m a -> Term n a
substituteMeta f = \case
  Var x          -> Var x
  Con con args   -> Con con (substituteMetaArg f <$> args)
  MetaVar m args -> instantiateMany (fmap (substituteMeta f) args !!? "substituteMeta") (f m)

(!!?) :: [a] -> String -> Int -> a
(xs !!? err) i
  | length xs > i = xs !! i
  | otherwise     = error ("index out of range (list size is " <> show (length xs) <> ", but index queried is " <> show i <> "): " <> err)

substituteMetaArg :: (m -> Term n (IncMany a)) -> ArgTerm m a -> ArgTerm n a
substituteMetaArg f = \case
  Regular t -> Regular (substituteMeta f t)
  Scoped s  -> Scoped (substituteMeta (fmap (fmap S) . f) s)

substituteMeta' :: (m -> Maybe (Term m (IncMany a))) -> Term m a -> Term m a
substituteMeta' f = \case
  Var x          -> Var x
  Con con args   -> Con con (substituteMetaArg' f <$> args)
  MetaVar m args ->
    case f m of
      Nothing -> MetaVar m args'
      Just t  -> instantiateMany (args' !!? ("substituteMeta' " <> getVariable (unsafeCoerce m :: Variable))) t
    where
      args' = substituteMeta' f <$> args

substituteMetaArg' :: (m -> Maybe (Term m (IncMany a))) -> ArgTerm m a -> ArgTerm m a
substituteMetaArg' f = \case
  Regular t -> Regular (substituteMeta' f t)
  Scoped s  -> Scoped (substituteMeta' (fmap (fmap (fmap S)) . f) s)

defaultFreshVars :: IsString a => [a]
defaultFreshVars = mkDefaultFreshVars "x"

defaultFreshBoundVars :: IsString a => [a]
defaultFreshBoundVars = mkDefaultFreshVars "z"

defaultFreshMetaVars :: IsString a => [a]
defaultFreshMetaVars = mkDefaultFreshVars "m"

mkDefaultFreshVars :: IsString a => String -> [a]
mkDefaultFreshVars prefix = [ fromString (prefix <> toIndex i) | i <- [1..] ]
  where
    toIndex n = index
      where
        digitToSub c = chr ((ord c - ord '0') + ord '₀')
        index = map digitToSub (show n)
