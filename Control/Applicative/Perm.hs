{- |
Copyright: Andy Sonnenburg (c) 2012
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Applicative.Perm
       ( Perm
       , runPerm
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative
import Control.Monad.Perm.Internal (Perm,
                                    sum1,
                                    liftPerm,
                                    hoistPerm)

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
runPerm :: Alternative m => Perm m a -> m a
runPerm = sum1
