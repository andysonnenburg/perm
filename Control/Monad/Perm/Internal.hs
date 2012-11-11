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
       , sum1
       , sum1M
       , liftPerm
       , liftPlus
       , hoistPerm
       ) where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad hiding (ap)
import qualified Control.Monad as Monad (ap)
#if LANGUAGE_DefaultSignatures
import Control.Monad.Catch.Class (MonadThrow)
#else
import Control.Monad.Catch.Class (MonadThrow (throw))
#endif
import Control.Monad.Fix (MonadFix (mfix))
import Control.Monad.IO.Class (MonadIO (liftIO))
#if MIN_VERSION_mtl(2, 1, 0)
import Control.Monad.Reader.Class (MonadReader (ask, local, reader))
import Control.Monad.State.Class (MonadState (get, put, state))
#else
import Control.Monad.Reader.Class (MonadReader (ask, local))
import Control.Monad.State.Class (MonadState (get, put))
#endif
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Maybe (Maybe (Nothing, Just), fromMaybe)
import Data.Monoid (Monoid (mappend, mempty))

import Prelude (($), (.), flip, fst, id, snd, uncurry)

-- | The permutation applicative
data Perm m a where
  Plus :: PlusDict m -> Perm m a -> Perm m a -> Perm m a
  Ap :: ApDict m -> m (a -> b) -> Perm m a -> Perm m b
  Bind :: Monad m => m a -> (a -> Perm m b) -> Perm m b
  Fix :: MonadFix m => (a -> Perm m (a, b)) -> Perm m b
  Lift :: m a -> Perm m a

newtype PlusDict m =
  PlusDict { getPlusDict :: forall a . Maybe (m a -> m a -> m a)
           }

fromPlusDict :: (forall a . m a -> m a -> m a) ->
                PlusDict m ->
                m b -> m b -> m b
fromPlusDict d = fromMaybe d . getPlusDict

alternative :: Alternative m => PlusDict m
alternative = PlusDict (Just (<|>))

monadPlus :: MonadPlus m => PlusDict m
monadPlus = PlusDict (Just mplus)

unit :: PlusDict m
unit = PlusDict Nothing

type ApDict m = forall a b . m (a -> b) -> m a -> m b

applicative :: Applicative m => ApDict m
applicative = (<*>)

monad :: Monad m => ApDict m
monad = Monad.ap

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
sum1 :: Alternative m => Perm m a -> m a
sum1 m = runPerm m (<|>)

-- | Unwrap a 'Perm', combining actions using the 'MonadPlus' for @f@.
sum1M :: MonadPlus m => Perm m a -> m a
sum1M m = runPerm m mplus

runPerm :: Perm m b -> (forall a . m a -> m a -> m a) -> m b
runPerm (Plus x m n) d = fromPlusDict d x (runPerm m d) (runPerm n d)
runPerm (Ap ap f a) plus = f `ap` runPerm a plus
runPerm (Bind m k) plus = m >>= \ a -> runPerm (k a) plus
runPerm (Fix k) plus = liftM snd $ mfix $ \ ~(a, _) -> runPerm (k a) plus
runPerm (Lift m) _ = m

-- | A version of 'lift' that can be used without a 'Monad' for @m@.
liftPerm :: m a -> Perm m a
liftPerm = Lift

liftPlus :: (forall a . m a -> m a -> m a) ->
            Perm m b -> Perm m b -> Perm m b
liftPlus plus = Plus (PlusDict (Just plus))

{- |
Lift a monad homomorphism from @m@ to @n@ into a monad homomorphism from
@'Perm' m@ to @'Perm' n@.
-}
hoistPerm :: MonadFix n => (forall a . m a -> n a) -> Perm m b -> Perm n b
hoistPerm f (Plus _ m n) = Plus unit (hoistPerm f m) (hoistPerm f n)
hoistPerm f (Ap _ g a) = Ap monad (f g) (hoistPerm f a)
hoistPerm f (Bind m k) = Bind (f m) (hoistPerm f . k)
hoistPerm f (Fix k) = Fix $ hoistPerm f . k
hoistPerm f (Lift m) = Lift (f m)

instance Monoid (m a) => Monoid (Perm m a) where
  mappend = (<>)
  mempty = liftPerm mempty

instance Functor m => Functor (Perm m) where
  fmap f (Plus dict m n) = Plus dict (fmap f m) (fmap f n)
  fmap f (Ap ap g a) = Ap ap (fmap (f .) g) a
  fmap f (Bind m k) = Bind m (fmap f . k)
  fmap f (Fix k) = Fix $ fmap (second f) . k
  fmap f (Lift m) = Lift (fmap f m)

instance Applicative m => Applicative (Perm m) where
  pure = liftPerm . pure
  f <*> a = (f `apL` a) <> (f `apR` a)

infixl 4 `apL`, `apR`
apL, apR :: Applicative m => Perm m (a -> b) -> Perm m a -> Perm m b

Plus plus m n `apL` a = Plus plus (m `apL` a) (n `apL` a)
Ap ap f a `apL` b = Ap ap (uncurry <$> f) $ zipA a b
Bind m k `apL` a = Bind m ((<*> a) . k)
Fix k `apL` n = Fix $ \ a0 -> (\ ((a1, f'), a') -> (a1, f' a')) <$> zipAL (k a0) n
Lift f `apL` a = Ap applicative f a

f `apR` Plus plus m n = Plus plus (f `apR` m) (f `apR` n)
f `apR` Ap ap g a = Ap ap ((\ g' (f', a') -> f' (g' a')) <$> g) $ zipA f a
f `apR` Bind m k = Bind m ((f <*>) . k)
f `apR` Fix k = Fix $ fmap (\ (f', (a1, a')) -> (a1, f' a')) . zipAR f . k
f `apR` Lift a = Ap (<*>) (flip ($) <$> a) f

zipAL, zipAR :: Applicative m => Perm m a -> Perm m b -> Perm m (a, b)
zipAL a b = (,) <$> a `apL` b
zipAR a b = (,) <$> a `apR` b

instance Alternative m => Alternative (Perm m) where
  empty = liftPerm empty
  (<|>) = Plus alternative

instance MonadFix m => Monad (Perm m) where
  return = lift . return
  m >>= k = (m `bindL` k) <> (m `bindR` k)
  m >> n = liftM' snd $ zipM' m n
  fail = lift . fail

infixl 1 `bindL`, `bindR`
bindL, bindR :: MonadFix m => Perm m a -> (a -> Perm m b) -> Perm m b

Plus plus m n `bindL` k = Plus plus (m `bindL` k) (n `bindL` k)
Ap _ f a `bindL` k = Bind f $ \ f' -> a >>= k . f'
Bind m f `bindL` g = Bind m $ f >=> g
Fix k `bindL` k' = Fix $ \ a0 -> k a0 `bindL` \ (a1, a') -> liftM' (\ b -> (a1, b)) $ k' a'
Lift m `bindL` k = Bind m k

m `bindR` k = liftM' snd $ mfix $ zipMR m . k . fst

liftM' :: Monad m => (a -> b) -> Perm m a -> Perm m b
liftM' f (Plus dict m n) = Plus dict (liftM' f m) (liftM' f n)
liftM' f (Ap ap g a) = Ap ap (liftM (f .) g) a
liftM' f (Bind m k) = Bind m (liftM' f . k)
liftM' f (Fix k) = Fix $ liftM' (second f) . k
liftM' f (Lift m) = Lift (liftM f m)

zipM', zipML, zipMR :: Monad m => Perm m a -> Perm m b -> Perm m (a, b)

zipM' m n = zipML m n <> zipMR m n

zipML (Plus plus m n) b = Plus plus (zipML m b) (zipML n b)
zipML (Ap ap f a) b = Ap ap (liftM mapFst f) $ zipM' a b
zipML (Bind m k) n = Bind m $ \ a -> zipM' (k a) n
zipML (Fix k) n = Fix $ \ a0 -> liftM' (\ ((a1, a'), b') -> (a1, (a', b'))) $ zipML (k a0) n
zipML (Lift m) n = Ap monad (liftM (,) m) n

zipMR a (Plus plus m n) = Plus plus (zipMR a m) (zipMR a n)
zipMR a (Ap ap f b) = Ap ap (liftM fmap f) $ zipM' a b
zipMR m (Bind n k) = Bind n $ zipM' m . k
zipMR m (Fix k) = Fix $ liftM' (\ (a, (a', b)) -> (a', (a, b))) . zipMR m . k
zipMR m (Lift n) = Ap monad (liftM (flip (,)) n) m

instance (MonadFix m, MonadPlus m) => MonadPlus (Perm m) where
  mzero = lift mzero
  mplus = Plus monadPlus

instance MonadFix m => MonadFix (Perm m) where
  mfix f = Fix $ liftM' (join (,)) . f

instance MonadTrans Perm where
  lift = Lift

instance (MonadFix m, MonadIO m) => MonadIO (Perm m) where
  liftIO = lift . liftIO

instance (MonadFix m, MonadReader r m) => MonadReader r (Perm m) where
  ask = lift ask
  local f (Plus plus m n) = Plus plus (local f m) (local f n)
  local f (Ap ap g a) = Ap ap (local f g) (local f a)
  local f (Bind m k) = Bind (local f m) (local f . k)
  local f (Fix k) = Fix $ local f . k
  local f (Lift m) = Lift $ local f m
#if MIN_VERSION_mtl(2, 1, 0)
  reader = lift . reader
#endif

instance (MonadFix m, MonadState s m) => MonadState s (Perm m) where
  get = lift get
  put = lift . put
#if MIN_VERSION_mtl(2, 1, 0)
  state = lift . state
#endif

#ifdef LANGUAGE_DefaultSignatures
instance (MonadFix m, MonadThrow e m) => MonadThrow e (Perm m)
#else
instance (MonadFix m, MonadThrow e m) => MonadThrow e (Perm m) where
  throw = lift . throw
#endif

infixr 6 <>
(<>) :: Perm m a -> Perm m a -> Perm m a
(<>) = Plus unit

zipA :: Applicative m => m a -> m b -> m (a, b)
zipA m n = (,) <$> m <*> n

mapFst :: (a -> a') -> (a, b) -> (a', b)
mapFst f (a, b) = (f a, b)
