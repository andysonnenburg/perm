{-# LANGUAGE
    CPP
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
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Catch.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Foldable (foldr)
import Data.Monoid (mempty)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 704
import Data.Monoid ((<>))
#else
import Data.Monoid (Monoid, mappend)
#endif

import Prelude (Maybe (..), ($), (.), const, flip, fst, id, map, maybe)

#if !defined(__GLASGOW_HASKELL__) || __GLASGOW_HASKELL__ < 704
(<>) :: Monoid m => m -> m -> m
(<>) = mappend
{-# INLINE (<>) #-}
#endif

-- | The permutation applicative
type Perm = PermT

-- | The permutation monad
data PermT m a = Choice (Maybe a) [Branch m a]

data Branch m b where
  Ap :: PermT m (a -> b) -> m a -> Branch m b
  Bind :: Monad m => (a -> PermT m b) -> m a -> Branch m b

instance Functor (PermT m) where
  fmap f (Choice a xs) = Choice (f <$> a) (fmap f <$> xs)

instance Functor (Branch m) where
  fmap f (Ap perm m) = Ap (fmap (f .) perm) m
  fmap f (Bind k m) = Bind (fmap f . k) m

instance Applicative (PermT m) where
  pure a = Choice (pure a) mempty
  f@(Choice f' fs) <*> a@(Choice a' as) =
    Choice (f' <*> a') (fmap (`apB` a) fs <> fmap (f `apP`) as)
  (*>) = liftThen (*>)

apP :: PermT m (a -> b) -> Branch m a -> Branch m b
f `apP` Ap perm m = (f .@ perm) `Ap` m
f `apP` Bind k m = Bind ((f `ap`) . k) m

(.@) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

apB :: Branch m (a -> b) -> PermT m a -> Branch m b
Ap perm m `apB` a = flipA2 perm a `Ap` m
Bind k m `apB` a = Bind ((`ap` a) . k) m

flipA2 :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

instance Alternative (PermT m) where
  empty = liftZero empty
  (<|>) = plus

instance Monad m => Monad (PermT m) where
  return a = Choice (return a) mempty
  Choice Nothing xs >>= k = Choice Nothing (map (bindP k) xs)
  Choice (Just a) xs >>= k = case k a of
    Choice a' xs' -> Choice a' (map (bindP k) xs <> xs')
  (>>) = liftThen (>>)
  fail _ = Choice mzero mempty

bindP :: Monad m => (a -> PermT m b) -> Branch m a -> Branch m b
bindP k (Ap perm m) = Bind (\ a -> k . ($ a) =<< perm) m
bindP k (Bind k' m) = Bind (k <=< k') m

instance Monad m => MonadPlus (PermT m) where
  mzero = liftZero mzero
  mplus = plus

instance MonadTrans PermT where
  lift = liftPerm

instance MonadIO m => MonadIO (PermT m) where
  liftIO = lift . liftIO

instance MonadReader r m => MonadReader r (PermT m) where
  ask = lift ask
  local f (Choice a xs) = Choice a (map (localBranch f) xs)

localBranch :: MonadReader r m => (r -> r) -> Branch m a -> Branch m a
localBranch f (Ap perm m) = Ap (local f perm) (local f m)
localBranch f (Bind k m) = Bind (local f . k) (local f m)

instance MonadState s m => MonadState s (PermT m) where
  get = lift get
  put = lift . put

#ifdef LANGUAGE_DefaultSignatures
instance MonadThrow e m => MonadThrow e (PermT m)
#else
instance MonadThrow e m => MonadThrow e (PermT m) where
  throw = lift . throw
#endif

liftThen :: (Maybe a -> Maybe b -> Maybe b) ->
            PermT m a -> PermT m b -> PermT m b
liftThen thenMaybe m@(Choice m' ms) n@(Choice n' ns) =
  Choice (m' `thenMaybe` n') (map (`thenB` n) ms <> map (m `thenP`) ns)

thenP :: PermT m a -> Branch m b -> Branch m b
m `thenP` Ap perm m' = (m *> perm) `Ap` m'
m `thenP` Bind k m' = Bind ((m >>) . k) m'

thenB :: Branch m a -> PermT m b -> Branch m b
Ap perm m `thenB` n = (perm *> fmap const n) `Ap` m
Bind k m `thenB` n = Bind ((>> n) . k) m

liftZero :: Maybe a -> PermT m a
liftZero zeroMaybe = Choice zeroMaybe mempty

plus :: PermT m a -> PermT m a -> PermT m a
m@(Choice (Just _) _) `plus` _ = m
Choice Nothing xs `plus` Choice b ys = Choice b (xs <> ys)

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
runPerm :: Alternative m => Perm m a -> m a
runPerm = lower
  where
    lower (Choice a xs) = foldr ((<|>) . f) (maybe empty pure a) xs
    f (perm `Ap` m) = m <**> runPerm perm
    f (Bind k m) = m >>= runPerm . k

-- | Unwrap a 'PermT', combining actions using the 'MonadPlus' for @f@.
runPermT :: MonadPlus m => PermT m a -> m a
runPermT = lower
  where
    lower (Choice a xs) = foldr (mplus . f) (maybe mzero return a) xs
    f (perm `Ap` m) = flip ($) `liftM` m `ap` runPermT perm
    f (Bind k m) = m >>= runPermT . k

-- | A version of 'lift' without the @'Monad.Monad' m@ constraint
liftPerm :: m a -> PermT m a
liftPerm = Choice empty . pure . liftBranch

liftBranch :: m a -> Branch m a
liftBranch = Ap (Choice (pure id) mempty)

{- |
Lift a natural transformation from @m@ to @n@ into a natural transformation
from @'PermT'' c m@ to @'PermT'' c n@.
-}
hoistPerm :: Monad n => (forall a . m a -> n a) -> PermT m b -> PermT n b
hoistPerm f (Choice a xs) = Choice a (hoistBranch f <$> xs)

hoistBranch :: Monad n => (forall a . m a -> n a) -> Branch m b -> Branch n b
hoistBranch f (perm `Ap` m) = hoistPerm f perm `Ap` f m
hoistBranch f (Bind k m) = Bind (hoistPerm f . k) (f m)
