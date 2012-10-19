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

#if MIN_VERSION_base(4, 5, 0)
import Data.Monoid (Monoid (mappend, mempty), (<>))
#else
import Data.Monoid (Monoid (mappend, mempty))
#endif

import Prelude (($), (.), const, flip, id)

#if !MIN_VERSION_base(4, 5, 0)
(<>) :: Monoid m => m -> m -> m
(<>) = mappend
{-# INLINE (<>) #-}
#endif

-- | The permutation applicative
type Perm = PermT

-- | The permutation monad
data PermT m a = Choice (Option m a) (Branches m a)

data Option m a
  = Zero (ZeroDict m)
  | Return (Dict m) a

data Branches m a
  = Plus (PlusDict m) (Branches m a) (Branches m a)
  | Branch (Branch m a)
  | Nil

data Branch m b where
  Ap :: Dict m -> PermT m (a -> b) -> m a -> Branch m b
  Bind :: Monad m => (a -> PermT m b) -> m a -> Branch m b

type ZeroDict = PlusDict

data PlusDict m where
  Alternative :: Alternative m => PlusDict m
  MonadPlus :: MonadPlus m => PlusDict m
  Unit :: PlusDict m

data Dict m where
  Applicative :: Applicative m => Dict m
  Monad :: Monad m => Dict m

option :: m a -> Option m a -> m a
option _ (Zero Alternative) = empty
option _ (Zero MonadPlus) = mzero
option n (Zero Unit) = n
option _ (Return Applicative a) = pure a
option _ (Return Monad a) = return a

instance Monoid (Option m a) where
  mempty = Zero Unit
  Zero _ `mappend` r = r
  l `mappend` _ = l

instance Functor (Option m) where
  fmap _ (Zero dict) = Zero dict
  fmap f (Return dict a) = Return dict (f a)

instance Applicative m => Applicative (Option m) where
  pure = Return Applicative
  Return _ f <*> a = fmap f a
  Zero dict <*> _ = Zero dict

instance Alternative m => Alternative (Option m) where
  empty = Zero Alternative
  Zero _ <|> r = r
  l <|> _ = l

instance Monad m => Monad (Option m) where
  return = Return Monad
  Return _ a >>= k = k a
  Zero dict >>= _ = Zero dict
  Return _ _ >> k = k
  Zero dict >> _ = Zero dict
  fail _ = mempty

instance MonadPlus m => MonadPlus (Option m) where
  mzero = Zero MonadPlus
  Zero _ `mplus` r = r
  l `mplus` _ = l

mapB :: (Branch m a -> Branch m b) -> Branches m a -> Branches m b
mapB f (Plus dict m n) = Plus dict (mapB f m) (mapB f n)
mapB f (Branch x) = Branch (f x)
mapB _ Nil = Nil

orB :: Alternative m => Branches m a -> Branches m a -> Branches m a
orB = Plus Alternative

mplusB :: MonadPlus m => Branches m a -> Branches m a -> Branches m a
mplusB = Plus MonadPlus

sumB :: (Branch m a -> m a) -> m a -> (m a -> m a -> m a) -> Branches m a -> m a
sumB f zero plus = go
  where
    go (Plus Alternative m n) = go m <|> go n
    go (Plus MonadPlus m n) = go m `mplus` go n
    go (Plus Unit m n) = go m `plus` go n
    go (Branch x) = f x
    go Nil = zero

instance Monoid (Branches m a) where
  mempty = Nil
  mappend = Plus Unit

instance Functor (Branches m) where
  fmap f (Plus dict m n) = Plus dict (fmap f m) (fmap f n)
  fmap f (Branch a) = Branch (fmap f a)
  fmap _ Nil = Nil

instance Functor (PermT m) where
  fmap f (Choice a xs) = Choice (f <$> a) (f <$> xs)

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

instance MonadTrans PermT where
  lift = Choice mempty . Branch . Ap Monad (Choice (return id) mempty)

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

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
runPerm :: Alternative m => Perm m a -> m a
runPerm = lower
  where
    lower (Choice a xs) = sumB f (option empty a) (<|>) xs
    f (Ap Monad perm m) = flip ($) `liftM` m `ap` runPerm perm
    f (Ap _ perm m) = m <**> runPerm perm
    f (Bind k m) = m >>= runPerm . k

-- | Unwrap a 'PermT', combining actions using the 'MonadPlus' for @f@.
runPermT :: MonadPlus m => PermT m a -> m a
runPermT = lower
  where
    lower (Choice a xs) = sumB f (option mzero a) mplus xs
    f (Ap Applicative perm m) = m <**> runPermT perm
    f (Ap _ perm m) = flip ($) `liftM` m `ap` runPermT perm
    f (Bind k m) = m >>= runPermT . k

-- | A version of 'lift' that can be used with just an 'Applicative' for @m@.
liftPerm :: Applicative m => m a -> PermT m a
liftPerm = Choice mempty . Branch . liftBranch

liftBranch :: Applicative m => m a -> Branch m a
liftBranch = Ap Applicative (Choice (pure id) mempty)

{- |
Lift a monad homomorphism from @m@ to @n@ into a monad homomorphism from
@'PermT' m@ to @'PermT' n@.
-}
hoistPerm :: Monad n => (forall a . m a -> n a) -> PermT m b -> PermT n b
hoistPerm f (Choice a xs) = Choice (hoistOption a) (hoistBranches f xs)

hoistOption :: Monad n => Option m a -> Option n a
hoistOption (Zero _) = mempty
hoistOption (Return _ a) = Return Monad a

hoistBranches :: Monad n =>
                 (forall a . m a -> n a) -> Branches m b -> Branches n b
hoistBranches f (Plus _ m n) = Plus Unit (hoistBranches f m) (hoistBranches f n)
hoistBranches f (Branch x) = Branch (hoistBranch f x)
hoistBranches _ Nil = Nil

hoistBranch :: Monad n => (forall a . m a -> n a) -> Branch m b -> Branch n b
hoistBranch f (Ap _ perm m) = Ap Monad (hoistPerm f perm) (f m)
hoistBranch f (Bind k m) = Bind (hoistPerm f . k) (f m)
