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

import Prelude (($), (.), const, flip, fst, id, map)

-- | The permutation applicative
type Perm = PermT

-- | The permutation monad
data PermT m a = Choice (Option m a) (Branches m a)

data Branch m b where
  Ap :: Dict m -> PermT m (a -> b) -> m a -> Branch m b
  Bind :: Monad m => (a -> PermT m b) -> m a -> Branch m b

data Branches m a where
  Plus :: PlusDict m -> Branches m a -> Branches m a -> Branches m a
  Branch :: Branch m a -> Branches m a
  Nil :: Branches m a

data PlusDict m where
  Alternative :: Alternative m => PlusDict m
  MonadPlus :: MonadPlus m => PlusDict m

mapB :: (Branch m a -> Branch m b) -> Branches m a -> Branches m b
mapB f (Plus dict m n) = Plus dict (mapB f m) (mapB f n)
mapB f (Branch x) = Branch (f x)
mapB _ Nil = Nil

foldrB :: (Branch m a -> m a) -> m a -> Branches m a -> m a
foldrB f a = go
  where
    go (Plus Alternative m n) = go m <|> go n
    go (Plus MonadPlus m n) = go m `mplus` go n
    go (Branch x) = f x
    go Nil = a

orB :: Alternative m => Branches m a -> Branches m a -> Branches m a
orB = Plus Alternative

mplusB :: MonadPlus m => Branches m a -> Branches m a -> Branches m a
mplusB = Plus MonadPlus

instance Functor (Branches m) where
  fmap f (Plus dict m n) = Plus dict (fmap f m) (fmap f n)
  fmap f (Branch a) = Branch (fmap f a)
  fmap _ Nil = Nil

data Option m a
  = Zero
  | Return (Dict m) a

option :: m a -> Option m a -> m a
option n Zero = n
option _ (Return Applicative a) = pure a
option _ (Return Monad a) = return a

instance Functor (Option m) where
  fmap _ Zero = Zero
  fmap f (Return dict a) = Return dict (f a)

instance Applicative m => Applicative (Option m) where
  pure = Return Applicative
  Return _ f <*> a = fmap f a
  Zero <*> _ = Zero

instance Applicative m => Alternative (Option m) where
  empty = Zero
  Zero <|> r = r
  l <|> _ = l

instance Monad m => Monad (Option m) where
  return = Return Monad
  Return _ a >>= k = k a
  Zero >>= _ = Zero
  Return _ _ >> k = k
  Zero >> _ = Zero
  fail _ = Zero

instance Monad m => MonadPlus (Option m) where
  mzero = Zero
  Zero `mplus` r = r
  l `mplus` _ = l

data Dict m where
  Applicative :: Applicative m => Dict m
  Monad :: Monad m => Dict m

instance Functor (PermT m) where
  fmap f (Choice a xs) = Choice (f <$> a) (f <$> xs)
#if MIN_VERSION_base(4, 2, 0)
  a <$ Choice b xs = Choice (a <$ b) (a <$ xs)
#endif

instance Functor (Branch m) where
  fmap f (Ap dict perm m) = Ap dict (fmap (f .) perm) m
  fmap f (Bind k m) = Bind (fmap f . k) m
#if MIN_VERSION_base(4, 2, 0)
  a <$ Ap dict perm m = Ap dict (const a <$ perm) m
  a <$ Bind k m = Bind ((a <$) . k) m
#endif

instance Alternative m => Applicative (PermT m) where
  pure a = Choice (pure a) Nil
  f@(Choice f' fs) <*> a@(Choice a' as) =
    Choice (f' <*> a') (mapB (`apB` a) fs `orB` mapB (f `apP`) as)
#if MIN_VERSION_base(4, 2, 0)
  m@(Choice m' ms) *> n@(Choice n' ns) =
    Choice (m' *> n') (mapB (`thenBA` n) ms `orB` mapB (m `thenPA`) ns)
#endif

apP :: Alternative m => PermT m (a -> b) -> Branch m a -> Branch m b
f `apP` Ap _ perm m = Ap Applicative (f .@ perm) m
f `apP` Bind k m = Bind ((f <*>) . k) m

(.@) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

apB :: Alternative m => Branch m (a -> b) -> PermT m a -> Branch m b
Ap _ perm m `apB` a = Ap Applicative (flipA2 perm a) m
Bind k m `apB` a = Bind ((<*> a) . k) m

flipA2 :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

#if MIN_VERSION_base(4, 2, 0)
thenPA :: Alternative m => PermT m a -> Branch m b -> Branch m b
m `thenPA` Ap _ perm n = Ap Applicative (m *> perm) n
m `thenPA` Bind k n = Bind ((m *>) . k) n

thenBA :: Alternative m => Branch m a -> PermT m b -> Branch m b
Ap _ perm m `thenBA` n = Ap Applicative (perm *> fmap const n) m
Bind k m `thenBA` n = Bind ((*> n) . k) m
#endif

instance Alternative m => Alternative (PermT m) where
  empty = liftZero empty
  m@(Choice (Return _ _) _) <|> _ = m
  Choice Zero xs <|> Choice b ys = Choice b (xs `orB` ys)

instance MonadPlus m => Monad (PermT m) where
  return a = Choice (return a) Nil
  Choice Zero xs >>= k = Choice Zero (mapB (bindP k) xs)
  Choice (Return _ a) xs >>= k = case k a of
    Choice a' xs' -> Choice a' (mapB (bindP k) xs `mplusB` xs')
  m@(Choice m' ms) >> n@(Choice n' ns) =
    Choice (m' >> n') (mapB (`thenBM` n) ms `mplusB` mapB (m `thenPM`) ns)
  fail s = Choice (fail s) Nil

bindP :: MonadPlus m => (a -> PermT m b) -> Branch m a -> Branch m b
bindP k (Ap _ perm m) = Bind (\ a -> k . ($ a) =<< perm) m
bindP k (Bind k' m) = Bind (k <=< k') m

thenPM :: MonadPlus m => PermT m a -> Branch m b -> Branch m b
m `thenPM` Ap _ perm n = Ap Monad (m >> perm) n
m `thenPM` Bind k n = Bind ((m >>) . k) n

thenBM :: MonadPlus m => Branch m a -> PermT m b -> Branch m b
Ap _ perm m `thenBM` n = Ap Monad (perm >> fmap const n) m
Bind k m `thenBM` n = Bind ((>> n) . k) m

instance MonadPlus m => MonadPlus (PermT m) where
  mzero = liftZero mzero
  m@(Choice (Return _ _) _) `mplus` _ = m
  Choice Zero xs `mplus` Choice b ys = Choice b (xs `mplusB` ys)

instance MonadTrans PermT where
  lift = Choice mzero . Branch . Ap Monad (Choice (return id) Nil)

instance (MonadPlus m, MonadIO m) => MonadIO (PermT m) where
  liftIO = lift . liftIO

instance (MonadPlus m, MonadReader r m) => MonadReader r (PermT m) where
  ask = lift ask
  local f (Choice a xs) = Choice a (mapB (localBranch f) xs)
#if MIN_VERSION_mtl(2, 1, 0)
  reader = lift . reader
#endif

localBranch :: (MonadPlus m, MonadReader r m) =>
               (r -> r) -> Branch m a -> Branch m a
localBranch f (Ap dict perm m) = Ap dict (local f perm) (local f m)
localBranch f (Bind k m) = Bind (local f . k) (local f m)

instance (MonadPlus m, MonadState s m) => MonadState s (PermT m) where
  get = lift get
  put = lift . put
#if MIN_VERSION_mtl(2, 1, 0)
  state = lift . state
#endif

#ifdef LANGUAGE_DefaultSignatures
instance (MonadPlus m, MonadThrow e m) => MonadThrow e (PermT m)
#else
instance (MonadPlus m, MonadThrow e m) => MonadThrow e (PermT m) where
  throw = lift . throw
#endif

liftZero :: Option m a -> PermT m a
liftZero zeroOption = Choice zeroOption Nil

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
runPerm :: Alternative m => Perm m a -> m a
runPerm = lower
  where
    lower (Choice a xs) = foldrB f (option empty a) xs
    f (Ap Monad perm m) = flip ($) `liftM` m `ap` runPerm perm
    f (Ap _ perm m) = m <**> runPerm perm
    f (Bind k m) = m >>= runPerm . k

-- | Unwrap a 'PermT', combining actions using the 'MonadPlus' for @f@.
runPermT :: MonadPlus m => PermT m a -> m a
runPermT = lower
  where
    lower (Choice a xs) = foldrB f (option mzero a) xs
    f (Ap Applicative perm m) = m <**> runPermT perm
    f (Ap _ perm m) = flip ($) `liftM` m `ap` runPermT perm
    f (Bind k m) = m >>= runPermT . k

-- | A version of 'lift' that can be used with just an 'Applicative' for @m@.
liftPerm :: Applicative m => m a -> PermT m a
liftPerm = Choice empty . Branch . liftBranch

liftBranch :: Applicative m => m a -> Branch m a
liftBranch = Ap Applicative (Choice (pure id) Nil)
