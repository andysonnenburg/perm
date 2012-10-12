{-# LANGUAGE DataKinds, Rank2Types #-}
module Control.Applicative.Perm
       ( PermT
       , runPermT
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative (Alternative)
import qualified Control.Applicative.Perm.Internal as Internal

type PermT = Internal.PermT Internal.Alternative

runPermT :: Alternative m => PermT m a -> m a
runPermT = Internal.runApplicativePermT

liftPerm :: m a -> PermT m a
liftPerm = Internal.liftPerm

hoistPerm :: (forall a . m a -> n a) -> PermT m b -> PermT n b
hoistPerm = Internal.hoistPerm
