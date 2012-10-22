{-# LANGUAGE GADTs #-}
{- |
Copyright: Andy Sonnenburg (c) 2012
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Monad.Perm.Option
       ( Option (..)
       , option
       , hoistOption
       ) where

import Control.Applicative
import Control.Monad

import Data.Monoid

import Control.Monad.Perm.Dict

data Option m a where
  Zero :: ZeroDict m -> Option m a
  Return :: Dict m -> a -> Option m a
  Fail :: Monad m => String -> Option m a

option :: m a -> Option m a -> m a
option _ (Zero Alternative) = empty
option _ (Zero MonadPlus) = mzero
option n (Zero Unit) = n
option _ (Return Applicative a) = pure a
option _ (Return Monad a) = return a
option _ (Fail s) = fail s

hoistOption :: Monad n => Option m a -> Option n a
hoistOption (Zero _) = mempty
hoistOption (Return _ a) = Return Monad a
hoistOption (Fail s) = Fail s

instance Monoid (Option m a) where
  mempty = Zero Unit
  l@(Return _ _) `mappend` _ = l
  _ `mappend` r = r

instance Functor (Option m) where
  fmap _ (Zero dict) = Zero dict
  fmap f (Return dict a) = Return dict (f a)
  fmap _ (Fail s) = Fail s

instance Applicative m => Applicative (Option m) where
  pure = Return Applicative
  Return _ f <*> a = fmap f a
  Zero dict <*> _ = Zero dict
  Fail s <*> _ = Fail s

instance Alternative m => Alternative (Option m) where
  empty = Zero Alternative
  l@(Return _ _) <|> _ = l
  _ <|> r = r

instance Monad m => Monad (Option m) where
  return = Return Monad
  Return _ a >>= k = k a
  Zero dict >>= _ = Zero dict
  Fail s >>= _ = Fail s
  Return _ _ >> k = k
  Zero dict >> _ = Zero dict
  Fail s >> _ = Fail s
  fail = Fail

instance MonadPlus m => MonadPlus (Option m) where
  mzero = Zero MonadPlus
  Zero _ `mplus` r = r
  l `mplus` _ = l
