{- |
Copyright: Andy Sonnenburg (c) 2012
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Monad.Perm
       ( Perm
       , runPerm
       , liftPerm
       , hoistPerm
       ) where

import Control.Monad
import Control.Monad.Perm.Internal (Perm,
                                    sum1M,
                                    liftPerm,
                                    hoistPerm)

-- | Unwrap a 'Perm', combining actions using the 'MonadPlus' for @f@.
runPerm :: MonadPlus m => Perm m a -> m a
runPerm = sum1M
