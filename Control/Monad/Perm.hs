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

import Control.Monad.Perm.Base (PermT,
                                runPermT,
                                liftPerm,
                                hoistPerm)
