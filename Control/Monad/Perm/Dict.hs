{-# LANGUAGE GADTs #-}
{- |
Copyright: Andy Sonnenburg (c) 2012
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Monad.Perm.Dict
       ( Dict (..)
       , PlusDict (..)
       , ZeroDict
       ) where

import Control.Applicative
import Control.Monad

data Dict m where
  Applicative :: Applicative m => Dict m
  Monad :: Monad m => Dict m

data PlusDict m where
  Alternative :: Alternative m => PlusDict m
  MonadPlus :: MonadPlus m => PlusDict m
  Unit :: PlusDict m

type ZeroDict = PlusDict
