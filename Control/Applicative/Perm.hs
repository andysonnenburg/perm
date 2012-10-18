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
       ) where

import Control.Monad.Perm.Internal (Perm,
                                    liftPerm,
                                    runPerm)
