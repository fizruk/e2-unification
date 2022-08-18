{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UndecidableInstances       #-}
-- | Fresh name supply monad
module Control.Monad.Fresh where

import           Control.Applicative
import           Control.Monad.Identity
import           Control.Monad.Logic
import           Control.Monad.State
import           Control.Monad.Writer

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
        return v

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

