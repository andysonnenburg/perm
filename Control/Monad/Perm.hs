{-# LANGUAGE DataKinds, Rank2Types #-}
module Control.Monad.Perm
       ( PermT
       , runPermT
       , liftPerm
       , hoistPerm
       ) where

import qualified Control.Applicative.Perm.Internal as Internal
import Control.Monad (MonadPlus)

type PermT = Internal.PermT Internal.MonadPlus

runPermT :: MonadPlus m => PermT m a -> m a
runPermT = Internal.runMonadPermT

liftPerm :: m a -> PermT m a
liftPerm = Internal.liftPerm

hoistPerm :: (forall a . m a -> n a) -> PermT m b -> PermT n b
hoistPerm = Internal.hoistPerm
