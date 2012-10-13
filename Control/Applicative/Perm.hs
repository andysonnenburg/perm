{-# LANGUAGE ConstraintKinds, Rank2Types #-}
{- |
Copyright: Andy Sonnenburg (c) 2012
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Applicative.Perm
       ( PermT
       , runPermT
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative (Alternative, Applicative)
import Control.Applicative.Perm.Internal (PermT,
                                          hoistPerm,
                                          liftPerm,
                                          runApplicativePermT)

runPermT :: Alternative m => PermT Applicative m a -> m a
runPermT = runApplicativePermT
