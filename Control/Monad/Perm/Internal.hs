{-# LANGUAGE
    DataKinds
  , ExistentialQuantification
  , FlexibleInstances
  , GADTs
  , MultiParamTypeClasses
  , Rank2Types
  , UndecidableInstances #-}
{- |
Copyright: Andy Sonnenburg (c) 2012
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Monad.Perm.Internal
       ( Perm
       , runPerm
       , PermT
       , runPermT
       , PermT'
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative hiding (Applicative)
import qualified Control.Applicative as Applicative (Applicative)
import Control.Monad hiding (Monad)
import qualified Control.Monad as Monad (Monad)
import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.RWS.Class
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Foldable (foldr)
import Data.Monoid ((<>), mempty)

import Prelude (Maybe (..), ($), (.), const, flip, id, map, maybe)

-- | The permutation applicative
type Perm = PermT' Applicative

-- | The permutation monad
type PermT = PermT' Monad

{- |
The permutation action, available as either an 'Applicative.Applicative'
or a 'Monad.Monad', determined by the combinators used.
-}
data PermT' c m a = Choice (Maybe a) [Branch c m a]

data Branch c m b where
  Ap :: PermT' c m (a -> b) -> m a -> Branch c m b
  Bind :: (a -> PermT m b) -> m a -> Branch Monad m b

data Constraint = Applicative | Monad

instance Functor (PermT' c m) where
  fmap f (Choice a xs) = Choice (f <$> a) (fmap f <$> xs)

instance Functor (Branch c m) where
  fmap f (Ap perm m) = Ap (fmap (f .) perm) m
  fmap f (Bind k m) = Bind (fmap f . k) m

instance Applicative.Applicative (PermT' c m) where
  pure a = Choice (pure a) mempty
  f@(Choice f' fs) <*> a@(Choice a' as) =
    Choice (f' <*> a') (fmap (`apB` a) fs <> fmap (f `apP`) as)
  (*>) = liftThen (*>)

instance Alternative (PermT' c m) where
  empty = liftZero empty
  (<|>) = plus

instance Monad.Monad (PermT m) where
  return a = Choice (return a) mempty
  Choice Nothing xs >>= k = Choice Nothing (map (bindP k) xs)
  Choice (Just a) xs >>= k = case k a of
    Choice a' xs' -> Choice a' (map (bindP k) xs <> xs')
  (>>) = liftThen (>>)
  fail _ = Choice mzero mempty

bindP :: (a -> PermT m b) -> Branch Monad m a -> Branch Monad m b
bindP k (Ap perm m) = Bind (\ a -> k . ($ a) =<< perm) m
bindP k (Bind k' m) = Bind (k <=< k') m

instance MonadPlus (PermT m) where
  mzero = liftZero mzero
  mplus = plus

instance MonadTrans (PermT' c) where
  lift = liftPerm

instance MonadIO m => MonadIO (PermT m) where
  liftIO = lift . liftIO

instance MonadError e m => MonadError e (PermT m) where
  throwError = lift . throwError

instance MonadRWS r w s m => MonadRWS r w s (PermT m)

instance MonadReader r m => MonadReader r (PermT m) where
  ask = lift ask
  local f (Choice a xs) = Choice a (map (localBranch f) xs)

localBranch :: MonadReader r m =>
               (r -> r) -> Branch Monad m a -> Branch Monad m a
localBranch f (Ap perm m) = Ap (local f perm) (local f m)
localBranch f (Bind k m) = Bind (local f . k) (local f m)

instance MonadState s m => MonadState s (PermT m) where
  get = lift get
  put = lift . put

instance MonadWriter w m => MonadWriter w (PermT m) where
  tell = lift . tell
  listen (Choice a xs) = Choice (flip (,) mempty <$> a) (map listenBranch xs)

listenBranch :: MonadWriter w m => Branch Monad m a -> Branch Monad m (a, w)
listenBranch (Ap perm m) =
  liftM (\ (f, y) (a, x) -> (f a, x <> y)) (listen perm) `Ap` listen m
listenBranch (Bind k m) =
  Bind (\ (a, w) -> liftM ((<> w) <$>) $ listen $ k a) (listen m)

apP :: PermT' c m (a -> b) -> Branch c m a -> Branch c m b
f `apP` Ap perm m = (f .@ perm) `Ap` m
f `apP` Bind k m = Bind ((f `ap`) . k) m

(.@) :: Applicative.Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

apB :: Branch c m (a -> b) -> PermT' c m a -> Branch c m b
Ap perm m `apB` a = flipA2 perm a `Ap` m
Bind k m `apB` a = Bind ((`ap` a) . k) m

flipA2 :: Applicative.Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

liftThen :: (Maybe a -> Maybe b -> Maybe b) ->
            PermT' c m a -> PermT' c m b -> PermT' c m b
liftThen thenMaybe m@(Choice m' ms) n@(Choice n' ns) =
  Choice (m' `thenMaybe` n') (map (`thenB` n) ms <> map (m `thenP`) ns)

thenP :: PermT' c m a -> Branch c m b -> Branch c m b
m `thenP` Ap perm m' = (m *> perm) `Ap` m'
m `thenP` Bind k m' = Bind ((m >>) . k) m'

thenB :: Branch c m a -> PermT' c m b -> Branch c m b
Ap perm m `thenB` n = (perm *> fmap const n) `Ap` m
Bind k m `thenB` n = Bind ((>> n) . k) m

liftZero :: Maybe a -> PermT' c m a
liftZero zeroMaybe = Choice zeroMaybe mempty

plus :: PermT' c m a -> PermT' c m a -> PermT' c m a
m@(Choice (Just _) _) `plus` _ = m
Choice Nothing xs `plus` Choice b ys = Choice b (xs <> ys)

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
runPerm :: Alternative m => Perm m a -> m a
runPerm = lower
  where
    lower (Choice a xs) = foldr ((<|>) . f) (maybe empty pure a) xs
    f (perm `Ap` m) = m <**> runPerm perm

-- | Unwrap a 'PermT', combining actions using the 'MonadPlus' for @f@.
runPermT :: MonadPlus m => PermT m a -> m a
runPermT = lower
  where
    lower (Choice a xs) = foldr (mplus . f) (maybe mzero return a) xs
    f (perm `Ap` m) = flip ($) `liftM` m `ap` runPermT perm
    f (Bind k m) = m >>= runPermT . k

-- | A version of 'lift' without the @'Monad.Monad' m@ constraint
liftPerm :: m a -> PermT' c m a
liftPerm = Choice empty . pure . liftBranch

liftBranch :: m a -> Branch c m a
liftBranch = Ap (Choice (pure id) mempty)

{- |
Lift a natural transformation from @m@ to @n@ into a natural transformation
from @'PermT' c m@ to @'PermT' c n@.
-}
hoistPerm :: (forall a . m a -> n a) -> PermT' c m b -> PermT' c n b
hoistPerm f (Choice a xs) = Choice a (hoistBranch f <$> xs)

hoistBranch :: (forall a . m a -> n a) -> Branch c m b -> Branch c n b
hoistBranch f (perm `Ap` m) = hoistPerm f perm `Ap` f m
hoistBranch f (Bind k m) = Bind (hoistPerm f . k) (f m)
