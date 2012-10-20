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
module Control.Monad.Perm.Base
       ( Perm
       , runPerm
       , PermT
       , runPermT
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative
import Control.Monad
#if LANGUAGE_DefaultSignatures
import Control.Monad.Catch.Class (MonadThrow)
#else
import Control.Monad.Catch.Class (MonadThrow (throw))
#endif
import Control.Monad.IO.Class (MonadIO (liftIO))
#if MIN_VERSION_mtl(2, 1, 0)
import Control.Monad.Reader.Class (MonadReader (ask, local, reader))
import Control.Monad.State.Class (MonadState (get, put, state))
#else
import Control.Monad.Reader.Class (MonadReader (ask, local))
import Control.Monad.State.Class (MonadState (get, put))
#endif
import Control.Monad.Trans.Class (MonadTrans (lift))

#if MIN_VERSION_base(4, 5, 0)
import Data.Monoid (Monoid (mappend, mempty), (<>))
#else
import Data.Monoid (Monoid (mappend, mempty))
#endif

import Prelude (($), (.), const, flip, id)

import Control.Monad.Perm.Dict
import Control.Monad.Perm.Option

#if !MIN_VERSION_base(4, 5, 0)
(<>) :: Monoid m => m -> m -> m
(<>) = mappend
{-# INLINE (<>) #-}
#endif

-- | The permutation applicative
type Perm = PermT

-- | The permutation monad
data PermT m a = Choice (Option m a) (Branches m a)

data Branches m a
  = Nil
  | Tip (Branch m a)
  | Bin (PlusDict m) (Branches m a) (Branches m a)

data Branch m b where
  Ap :: Dict m -> PermT m (a -> b) -> m a -> Branch m b
  Bind :: Monad m => (a -> PermT m b) -> m a -> Branch m b

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
runPerm :: Alternative m => Perm m a -> m a
runPerm (Choice a xs) = sumB f (option empty a) (<|>) xs
  where
    f (Ap Monad perm m) = flip ($) `liftM` m `ap` runPerm perm
    f (Ap _ perm m) = m <**> runPerm perm
    f (Bind k m) = m >>= runPerm . k

-- | Unwrap a 'PermT', combining actions using the 'MonadPlus' for @f@.
runPermT :: MonadPlus m => PermT m a -> m a
runPermT (Choice a xs) = sumB f (option mzero a) mplus xs
  where
    f (Ap Applicative perm m) = m <**> runPermT perm
    f (Ap _ perm m) = flip ($) `liftM` m `ap` runPermT perm
    f (Bind k m) = m >>= runPermT . k

sumB :: (Branch m a -> m a) -> m a -> (m a -> m a -> m a) -> Branches m a -> m a
sumB f zero plus = go
  where
    go Nil = zero
    go (Tip x) = f x
    go (Bin Alternative m n) = go m <|> go n
    go (Bin MonadPlus m n) = go m `mplus` go n
    go (Bin Unit m n) = go m `plus` go n

-- | A version of 'lift' that can be used with just an 'Applicative' for @m@.
liftPerm :: Applicative m => m a -> PermT m a
liftPerm = Choice mempty . liftBranches

liftBranches :: Applicative m => m a -> Branches m a
liftBranches = Tip . liftBranch

liftBranch :: Applicative m => m a -> Branch m a
liftBranch = Ap Applicative (Choice (pure id) mempty)

{- |
Lift a monad homomorphism from @m@ to @n@ into a monad homomorphism from
@'PermT' m@ to @'PermT' n@.
-}
hoistPerm :: Monad n => (forall a . m a -> n a) -> PermT m b -> PermT n b
hoistPerm f (Choice a xs) = Choice (hoistOption a) (hoistBranches f xs)

hoistBranches :: Monad n =>
                 (forall a . m a -> n a) -> Branches m b -> Branches n b
hoistBranches _ Nil = Nil
hoistBranches f (Tip x) = Tip (hoistBranch f x)
hoistBranches f (Bin _ m n) = Bin Unit (hoistBranches f m) (hoistBranches f n)

hoistBranch :: Monad n => (forall a . m a -> n a) -> Branch m b -> Branch n b
hoistBranch f (Ap _ perm m) = Ap Monad (hoistPerm f perm) (f m)
hoistBranch f (Bind k m) = Bind (hoistPerm f . k) (f m)

instance Functor (PermT m) where
  fmap f (Choice a xs) = Choice (f <$> a) (f <$> xs)

instance Functor (Branches m) where
  fmap _ Nil = Nil
  fmap f (Tip a) = Tip (fmap f a)
  fmap f (Bin dict m n) = Bin dict (fmap f m) (fmap f n)

instance Functor (Branch m) where
  fmap f (Ap dict perm m) = Ap dict (fmap (f .) perm) m
  fmap f (Bind k m) = Bind (fmap f . k) m

instance Applicative m => Applicative (PermT m) where
  pure a = Choice (pure a) mempty
  f@(Choice f' fs) <*> a@(Choice a' as) =
    Choice (f' <*> a') (mapB (`apB` a) fs <> mapB (f `apP`) as)

apP :: Applicative m => PermT m (a -> b) -> Branch m a -> Branch m b
f `apP` Ap _ perm m = Ap Applicative (f .@ perm) m
f `apP` Bind k m = Bind ((f <*>) . k) m

(.@) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

apB :: Applicative m => Branch m (a -> b) -> PermT m a -> Branch m b
Ap _ perm m `apB` a = Ap Applicative (flipA2 perm a) m
Bind k m `apB` a = Bind ((<*> a) . k) m

flipA2 :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

instance Alternative m => Alternative (PermT m) where
  empty = Choice empty mempty
  m@(Choice (Return _ _) _) <|> _ = m
  Choice (Zero _) xs <|> Choice b ys = Choice b (xs `orB` ys)

orB :: Alternative m => Branches m a -> Branches m a -> Branches m a
orB = Bin Alternative

instance Monad m => Monad (PermT m) where
  return a = Choice (return a) mempty
  Choice (Zero dict) xs >>= k = Choice (Zero dict) (mapB (bindP k) xs)
  Choice (Return _ a) xs >>= k = case k a of
    Choice a' xs' -> Choice a' (mapB (bindP k) xs <> xs')
  m@(Choice m' ms) >> n@(Choice n' ns) =
    Choice (m' >> n') (mapB (`thenBM` n) ms <> mapB (m `thenPM`) ns)
  fail s = Choice (fail s) mempty

bindP :: Monad m => (a -> PermT m b) -> Branch m a -> Branch m b
bindP k (Ap _ perm m) = Bind (\ a -> k . ($ a) =<< perm) m
bindP k (Bind k' m) = Bind (k <=< k') m

thenPM :: Monad m => PermT m a -> Branch m b -> Branch m b
m `thenPM` Ap _ perm n = Ap Monad (m >> perm) n
m `thenPM` Bind k n = Bind ((m >>) . k) n

thenBM :: Monad m => Branch m a -> PermT m b -> Branch m b
Ap _ perm m `thenBM` n = Ap Monad (perm >> fmap const n) m
Bind k m `thenBM` n = Bind ((>> n) . k) m

instance MonadPlus m => MonadPlus (PermT m) where
  mzero = Choice mzero mempty
  m@(Choice (Return _ _) _) `mplus` _ = m
  Choice (Zero _) xs `mplus` Choice b ys = Choice b (xs `mplusB` ys)

mplusB :: MonadPlus m => Branches m a -> Branches m a -> Branches m a
mplusB = Bin MonadPlus

instance MonadTrans PermT where
  lift = Choice mempty . Tip . Ap Monad (Choice (return id) mempty)

instance Monoid (Branches m a) where
  mempty = Nil
  mappend = Bin Unit

instance MonadIO m => MonadIO (PermT m) where
  liftIO = lift . liftIO

instance MonadReader r m => MonadReader r (PermT m) where
  ask = lift ask
  local f (Choice a xs) = Choice a (mapB (localBranch f) xs)
#if MIN_VERSION_mtl(2, 1, 0)
  reader = lift . reader
#endif

localBranch :: MonadReader r m => (r -> r) -> Branch m a -> Branch m a
localBranch f (Ap dict perm m) = Ap dict (local f perm) (local f m)
localBranch f (Bind k m) = Bind (local f . k) (local f m)

instance MonadState s m => MonadState s (PermT m) where
  get = lift get
  put = lift . put
#if MIN_VERSION_mtl(2, 1, 0)
  state = lift . state
#endif

#ifdef LANGUAGE_DefaultSignatures
instance MonadThrow e m => MonadThrow e (PermT m)
#else
instance MonadThrow e m => MonadThrow e (PermT m) where
  throw = lift . throw
#endif

mapB :: (Branch m a -> Branch m b) -> Branches m a -> Branches m b
mapB _ Nil = Nil
mapB f (Tip x) = Tip (f x)
mapB f (Bin dict m n) = Bin dict (mapB f m) (mapB f n)
