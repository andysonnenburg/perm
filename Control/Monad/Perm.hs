{-# LANGUAGE ConstraintKinds, Rank2Types #-}
{- |
Copyright: Andy Sonnenburg (c) 2012
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Monad.Perm
       ( PermT
       , runPermT
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative.Perm.Internal (PermT,
                                          liftPerm,
                                          hoistPerm,
                                          runMonadPermT)
import Control.Monad (MonadPlus)

-- | Unwrap a 'PermT', combining actions using the 'MonadPlus' for @f@.
runPermT :: MonadPlus m => PermT Monad m a -> m a
runPermT = runMonadPermT
