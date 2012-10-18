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

import Data.Foldable (foldr)
#if MIN_VERSION_base(4, 5, 0)
import Data.Monoid ((<>), mempty)
#else
import Data.Monoid (Monoid, mappend, mempty)
#endif

import Prelude (($), (.), const, flip, fst, id, map)

#if !MIN_VERSION_base(4, 5, 0)
(<>) :: Monoid m => m -> m -> m
(<>) = mappend
{-# INLINE (<>) #-}
#endif

-- | The permutation applicative
type Perm = PermT

-- | The permutation monad
data PermT m a = Choice (Maybe m a) [Branch m a]

data Branch m b where
  Ap :: Dict m -> PermT m (a -> b) -> m a -> Branch m b
  Bind :: Monad m => (a -> PermT m b) -> m a -> Branch m b

data Maybe m a
  = Nothing
  | Just (Dict m) a

maybe :: m a -> Maybe m a -> m a
maybe n Nothing = n
maybe _ (Just Applicative a) = pure a
maybe _ (Just Monad a) = return a

instance Functor (Maybe m) where
  fmap _ Nothing = Nothing
  fmap f (Just dict a) = Just dict (f a)

instance Applicative m => Applicative (Maybe m) where
  pure = Just Applicative
  Just _ f <*> a = fmap f a
  Nothing <*> _ = Nothing

instance Applicative m => Alternative (Maybe m) where
  empty = Nothing
  Nothing <|> r = r
  l <|> _ = l

instance Monad m => Monad (Maybe m) where
  return = Just Monad
  Just _ a >>= k = k a
  Nothing >>= _ = Nothing
  Just _ _ >> k = k
  Nothing >> _ = Nothing
  fail _ = Nothing

instance Monad m => MonadPlus (Maybe m) where
  mzero = Nothing
  Nothing `mplus` r = r
  l `mplus` _ = l

data Dict m where
  Applicative :: Applicative m => Dict m
  Monad :: Monad m => Dict m

instance Functor (PermT m) where
  fmap f (Choice a xs) = Choice (f <$> a) (fmap f <$> xs)
#if MIN_VERSION_base(4, 2, 0)
  a <$ Choice b xs = Choice (a <$ b) (fmap (a <$) xs)
#endif

instance Functor (Branch m) where
  fmap f (Ap dict perm m) = Ap dict (fmap (f .) perm) m
  fmap f (Bind k m) = Bind (fmap f . k) m
#if MIN_VERSION_base(4, 2, 0)
  a <$ Ap dict perm m = Ap dict (const a <$ perm) m
  a <$ Bind k m = Bind ((a <$) . k) m
#endif

instance Applicative m => Applicative (PermT m) where
  pure a = Choice (pure a) mempty
  f@(Choice f' fs) <*> a@(Choice a' as) =
    Choice (f' <*> a') (fmap (`apB` a) fs <> fmap (f `apP`) as)
#if MIN_VERSION_base(4, 2, 0)
  m@(Choice m' ms) *> n@(Choice n' ns) =
    Choice (m' *> n') (map (`thenBA` n) ms <> map (m `thenPA`) ns)
#endif

apP :: Applicative m => PermT m (a -> b) -> Branch m a -> Branch m b
f `apP` Ap _ perm m = Ap Applicative (f .@ perm) m
f `apP` Bind k m = Bind ((f `ap`) . k) m

(.@) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

apB :: Applicative m => Branch m (a -> b) -> PermT m a -> Branch m b
Ap _ perm m `apB` a = Ap Applicative (flipA2 perm a) m
Bind k m `apB` a = Bind ((`ap` a) . k) m

flipA2 :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

#if MIN_VERSION_base(4, 2, 0)
thenPA :: Applicative m => PermT m a -> Branch m b -> Branch m b
m `thenPA` Ap _ perm n = Ap Applicative (m *> perm) n
m `thenPA` Bind k n = Bind ((m *>) . k) n

thenBA :: Applicative m => Branch m a -> PermT m b -> Branch m b
Ap _ perm m `thenBA` n = Ap Applicative (perm *> fmap const n) m
Bind k m `thenBA` n = Bind ((*> n) . k) m
#endif

instance Applicative m => Alternative (PermT m) where
  empty = liftZero empty
  (<|>) = plus

instance Monad m => Monad (PermT m) where
  return a = Choice (return a) mempty
  Choice Nothing xs >>= k = Choice Nothing (map (bindP k) xs)
  Choice (Just _ a) xs >>= k = case k a of
    Choice a' xs' -> Choice a' (map (bindP k) xs <> xs')
  m@(Choice m' ms) >> n@(Choice n' ns) =
    Choice (m' >> n') (map (`thenBM` n) ms <> map (m `thenPM`) ns)
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

instance Monad m => MonadPlus (PermT m) where
  mzero = liftZero mzero
  mplus = plus

instance MonadTrans PermT where
  lift = Choice mzero . pure . Ap Monad (Choice (return id) mempty)

instance MonadIO m => MonadIO (PermT m) where
  liftIO = lift . liftIO

instance MonadReader r m => MonadReader r (PermT m) where
  ask = lift ask
  local f (Choice a xs) = Choice a (map (localBranch f) xs)
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

liftZero :: Maybe m a -> PermT m a
liftZero zeroMaybe = Choice zeroMaybe mempty

plus :: PermT m a -> PermT m a -> PermT m a
m@(Choice (Just _ _) _) `plus` _ = m
Choice Nothing xs `plus` Choice b ys = Choice b (xs <> ys)

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
runPerm :: Alternative m => Perm m a -> m a
runPerm = lower
  where
    lower (Choice a xs) = foldr ((<|>) . f) (maybe empty a) xs
    f (Ap Monad perm m) = flip ($) `liftM` m `ap` runPerm perm
    f (Ap _ perm m) = m <**> runPerm perm
    f (Bind k m) = m >>= runPerm . k

-- | Unwrap a 'PermT', combining actions using the 'MonadPlus' for @f@.
runPermT :: MonadPlus m => PermT m a -> m a
runPermT = lower
  where
    lower (Choice a xs) = foldr (mplus . f) (maybe mzero a) xs
    f (Ap Applicative perm m) = m <**> runPermT perm
    f (Ap _ perm m) = flip ($) `liftM` m `ap` runPermT perm
    f (Bind k m) = m >>= runPermT . k

-- | A version of 'lift' that can be used with just an 'Applicative' for m.
liftPerm :: Applicative m => m a -> PermT m a
liftPerm = Choice empty . pure . liftBranch

liftBranch :: Applicative m => m a -> Branch m a
liftBranch = Ap Applicative (Choice (pure id) mempty)

{- |
Lift a monad homomorphism from @m@ to @n@ into a monad homomorphism from
@'PermT' m@ to @'PermT' n@.
-}
hoistPerm :: Monad n => (forall a . m a -> n a) -> PermT m b -> PermT n b
hoistPerm f (Choice a xs) = Choice (hoistMaybe a) (hoistBranch f <$> xs)

hoistMaybe :: Monad n => Maybe m a -> Maybe n a
hoistMaybe Nothing = Nothing
hoistMaybe (Just _ a) = Just Monad a

hoistBranch :: Monad n => (forall a . m a -> n a) -> Branch m b -> Branch n b
hoistBranch f (Ap _ perm m) = Ap Monad (hoistPerm f perm) (f m)
hoistBranch f (Bind k m) = Bind (hoistPerm f . k) (f m)
