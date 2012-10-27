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

import Control.Monad
import Control.Monad.Perm.Internal (Perm,
                                    sum1M,
                                    liftPerm,
                                    hoistPerm)

-- | The permutation monad
type PermT = Perm

-- | Unwrap a 'Perm', combining actions using the 'MonadPlus' for @f@.
runPermT :: MonadPlus m => PermT m a -> m a
runPermT = sum1M
