{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
module E2.Term where

import           Unsafe.Coerce

import           Control.Applicative
import           Control.Monad       (ap)
import           Data.Char           (chr, ord)
import           Data.List           (intercalate)
import           Data.String         (IsString (..))

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

-- | An argument term (i.e. occuring in the list of arguments to a constructor).
data ArgTerm metavar var
  = Regular (Term metavar var)        -- ^ Regular subterm.
  | Scoped  (Term metavar (Inc var))  -- ^ Scoped subterm (introduces one bound variable).
  deriving (Eq, Show, Functor, Foldable, Traversable)

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

type ArgTerm' = ArgTerm Variable

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

-- * Substitutions

-- ** Variable substitution

-- | Substitute all variables in a term.
substitute :: (a -> Term m b) -> Term m a -> Term m b
substitute f = \case
  Var x          -> f x
  Con con args   -> Con con (substituteArg f <$> args)
  MetaVar m args -> MetaVar m (substitute f <$> args)

-- | Substitute all variables in an argument term.
substituteArg :: (a -> Term m b) -> ArgTerm m a -> ArgTerm m b
substituteArg f = \case
  Regular t -> Regular (substitute f t)
  Scoped s  -> Scoped (substitute f' s)
  where
    f' Z     = Var Z
    f' (S x) = S <$> f x

-- ** Meta substitution

-- | Substitute all meta variables in a term.
-- Note that here all metavariables must have a substitution defined.
substituteMeta :: (m -> Term n (IncMany a)) -> Term m a -> Term n a
substituteMeta f = \case
  Var x          -> Var x
  Con con args   -> Con con (substituteMetaArg f <$> args)
  MetaVar m args -> instantiateMany (fmap (substituteMeta f) args !!? "substituteMeta") (f m)

-- | Substitute all meta variables in an argument term.
-- Note that here all metavariables must have a substitution defined.
substituteMetaArg :: (m -> Term n (IncMany a)) -> ArgTerm m a -> ArgTerm n a
substituteMetaArg f = \case
  Regular t -> Regular (substituteMeta f t)
  Scoped s  -> Scoped (substituteMeta (fmap (fmap S) . f) s)

-- | Substitute some meta variables in a term.
-- Here, 'Nothing' means that corresponding meta variable should not be substituted
-- (but substitution may still take place in its parameters).
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

-- | Substitute some meta variables in an argument term.
-- Here, 'Nothing' means that corresponding meta variable should not be substituted
-- (but substitution may still take place in its parameters).
substituteMetaArg' :: (m -> Maybe (Term m (IncMany a))) -> ArgTerm m a -> ArgTerm m a
substituteMetaArg' f = \case
  Regular t -> Regular (substituteMeta' f t)
  Scoped s  -> Scoped (substituteMeta' (fmap (fmap (fmap S)) . f) s)

-- ** Renaming meta variables

-- | Rename meta variables in a term.
renameMeta :: (m -> n) -> Term m a -> Term n a
renameMeta f = \case
  Var x          -> Var x
  Con con args   -> Con con (renameMetaArg f <$> args)
  MetaVar m args -> MetaVar (f m) (renameMeta f <$> args)

-- | Rename meta variables in an argument term.
renameMetaArg :: (m -> n) -> ArgTerm m a -> ArgTerm n a
renameMetaArg f = \case
  Regular t -> Regular (renameMeta f t)
  Scoped s  -> Scoped (renameMeta f s)

-- * Default fresh names

-- | Default fresh names for variables:
--
-- >>> mapM_ putStrLn $ take 5 defaultFreshVars
-- x₁
-- x₂
-- x₃
-- x₄
-- x₅
defaultFreshVars :: IsString a => [a]
defaultFreshVars = mkDefaultFreshVars "x"

-- | Default stream of fresh names for bound variables.
--
-- >>> mapM_ putStrLn $ take 5 defaultFreshBoundVars
-- z₁
-- z₂
-- z₃
-- z₄
-- z₅
defaultFreshBoundVars :: IsString a => [a]
defaultFreshBoundVars = mkDefaultFreshVars "z"

-- | Default strem of fresh names for meta variables.
--
-- >>> mapM_ putStrLn $ take 5 defaultFreshMetaVars
-- m₁
-- m₂
-- m₃
-- m₄
-- m₅
defaultFreshMetaVars :: IsString a => [a]
defaultFreshMetaVars = mkDefaultFreshVars "m"

-- | Make an infinite stream of default names with numeric subscript.
--
-- >>> mapM_ putStrLn $ take 5 (mkDefaultFreshVars "example")
-- example₁
-- example₂
-- example₃
-- example₄
-- example₅
mkDefaultFreshVars :: IsString a => String -> [a]
mkDefaultFreshVars prefix = [ fromString (prefix <> toIndex i) | i <- [1..] ]
  where
    toIndex n = index
      where
        digitToSub c = chr ((ord c - ord '0') + ord '₀')
        index = map digitToSub (show n)

-- * Pretty-printing

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

-- | Pretty-print a variable (using a default name for the bound variable).
ppInc :: String -> Inc String -> String
ppInc def Z   = def
ppInc _ (S x) = x

-- | Pretty-print a variable (using a list of default names for the bound variables).
ppIncMany :: [String] -> IncMany String -> String
ppIncMany xs (B i) = (xs !!? "ppIncMany") i
ppIncMany _ (F x)  = x

-- * Helpers

-- | A version of '!!' with a custom error message.
(!!?) :: [a] -> String -> Int -> a
(xs !!? err) i
  | length xs > i = xs !! i
  | otherwise     = error ("index out of range (list size is " <> show (length xs) <> ", but index queried is " <> show i <> "): " <> err)

-- * De Bruijn indices as nested data types

-- | Add one (bound) variable.
data Inc var
  = Z     -- ^ The bound variable.
  | S var -- ^ A free variable (or another bound variable from the outside).
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Add arbitrarily many bound variables.
data IncMany var
  = B Int -- ^ The bound variable.
  | F var -- ^ A free variable (or another bound variable from the outside).
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Instantiate bound variables in a generalized term.
instantiateMany :: Monad f => (Int -> f a) -> f (IncMany a) -> f a
instantiateMany f t = t >>= \case
  B i -> f i
  F x -> return x

-- | Convert two scopes into one.
joinInc :: Inc (IncMany a) -> IncMany a
joinInc Z         = B 0
joinInc (S (B i)) = B (i + 1)
joinInc (S (F x)) = F x

-- | Commute scopes.
commuteInc :: Inc (IncMany a) -> IncMany (Inc a)
commuteInc Z         = F Z
commuteInc (S (B i)) = B i
commuteInc (S (F x)) = F (S x)

-- | Remove bound variables if possible.
removeInc :: Alternative f => Inc a -> f a
removeInc Z     = empty
removeInc (S x) = pure x

-- | Remove bound variables if possible.
removeIncMany :: Alternative f => IncMany a -> f a
removeIncMany (B _) = empty
removeIncMany (F x) = pure x

-- | Remove the first bound variable if possible.
decIncMany :: Alternative f => IncMany a -> f (IncMany a)
decIncMany (B 0) = empty
decIncMany (B i) = pure (B (i - 1))
decIncMany (F x) = pure (F x)

-- | Remove the first bound variable from a generalised term.
removeAllIncMany :: (Traversable t, Alternative f) => t (IncMany a) -> f (t a)
removeAllIncMany = traverse removeIncMany

