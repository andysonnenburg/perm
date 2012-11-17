{-# LANGUAGE
    CPP
  , FlexibleInstances
  , GADTs
  , MultiParamTypeClasses
  , Rank2Types
  , ScopedTypeVariables
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
       , liftAp
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
import Control.Monad.Cont.Class (MonadCont (callCC))
import Control.Monad.Error.Class (MonadError (catchError, throwError))
import Control.Monad.Fix (MonadFix (mfix))
import Control.Monad.IO.Class (MonadIO (liftIO))
#if MIN_VERSION_mtl (2, 1, 0)
import Control.Monad.Reader.Class (MonadReader (ask, local, reader))
import Control.Monad.State.Class (MonadState (get, put, state))
#else
import Control.Monad.Reader.Class (MonadReader (ask, local))
import Control.Monad.State.Class (MonadState (get, put))
#endif
import Control.Monad.Trans.Class (MonadTrans (lift))
#if MIN_VERSION_mtl (2, 1, 0)
import Control.Monad.Writer.Class (MonadWriter (listen, pass, tell, writer))
#else
import Control.Monad.Writer.Class (MonadWriter (listen, pass, tell))
#endif

import Data.Maybe (Maybe (Just, Nothing), fromMaybe)
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
hoistPerm f (Ap _ g a) = Ap Monad.ap (f g) (hoistPerm f a)
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
  (<*>) = liftAp (<*>)

liftAp :: forall c d m .
          Functor m =>
          (forall a b . m (a -> b) -> m a -> m b) ->
          Perm m (c -> d) -> Perm m c -> Perm m d
liftAp ap' = ap
  where
    infixl 4 `ap`, `apL`, `apR`
    ap, apL, apR :: Perm m (a -> b) -> Perm m a -> Perm m b

    f `ap` a = (f `apL` a) <> (f `apR` a)

    Plus dict m n `apL` a = Plus dict (m `apL` a) (n `apL` a)
    Ap dict f a `apL` b = Ap dict (uncurry <$> f) $ zipA a b
    Bind m k `apL` a = Bind m ((`ap` a) . k)
    Fix k `apL` n = Fix $ \ a0 -> (\ ((a1, f'), a') -> (a1, f' a')) <$> zipAL (k a0) n
    Lift f `apL` a = Ap ap' f a

    f `apR` Plus dict m n = Plus dict (f `apR` m) (f `apR` n)
    f `apR` Ap dict g a = Ap dict ((\ g' (f', a') -> f' (g' a')) <$> g) $ zipA f a
    f `apR` Bind m k = Bind m ((f `ap`) . k)
    f `apR` Fix k = Fix $ \ a0 -> (\ (f', (a1, a')) -> (a1, f' a')) <$> zipAR f (k a0)
    f `apR` Lift a = Ap ap' (flip ($) <$> a) f

    zipA, zipAL, zipAR :: Perm m a -> Perm m b -> Perm m (a, b)

    zipA a b = (,) <$> a `ap` b

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

Plus dict m n `bindL` k = Plus dict (m `bindL` k) (n `bindL` k)
Ap _ f a `bindL` k = Bind f $ \ f' -> a >>= k . f'
Bind m f `bindL` g = Bind m $ f >=> g
Fix k `bindL` k' = Fix $ \ a0 -> k a0 `bindL` \ (a1, a') -> liftM' ((,) a1) $ k' a'
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

zipML (Plus dict m n) b = Plus dict (zipML m b) (zipML n b)
zipML (Ap ap f a) b = Ap ap (liftM mapFst f) $ zipM' a b
zipML (Bind m k) n = Bind m $ \ a -> zipM' (k a) n
zipML (Fix k) n = Fix $ \ a0 -> liftM' (\ ((a1, a'), b') -> (a1, (a', b'))) $ zipML (k a0) n
zipML (Lift m) n = Ap Monad.ap (liftM (,) m) n

zipMR a (Plus dict m n) = Plus dict (zipMR a m) (zipMR a n)
zipMR a (Ap ap f b) = Ap ap (liftM fmap f) $ zipM' a b
zipMR m (Bind n k) = Bind n $ zipM' m . k
zipMR m (Fix k) = Fix $ \ a0 -> liftM' (\ (a, (a1, b)) -> (a1, (a, b))) $ zipMR m (k a0)
zipMR m (Lift n) = Ap Monad.ap (liftM (flip (,)) n) m

instance (MonadFix m, MonadPlus m) => MonadPlus (Perm m) where
  mzero = lift mzero
  mplus = Plus monadPlus

instance MonadFix m => MonadFix (Perm m) where
  mfix f = Fix $ liftM' (join (,)) . f

instance MonadTrans Perm where
  lift = Lift

instance (MonadFix m, MonadIO m) => MonadIO (Perm m) where
  liftIO = lift . liftIO

instance (MonadFix m, MonadPlus m, MonadCont m) => MonadCont (Perm m) where
  callCC f = lift $ callCC $ \ c -> sum1M (f (lift . c))

instance (MonadFix m, MonadPlus m, MonadError e m) => MonadError e (Perm m) where
  throwError = lift . throwError
  m `catchError` h = lift $ sum1M m `catchError` (sum1M . h)

instance (MonadFix m, MonadReader r m) => MonadReader r (Perm m) where
  ask = lift ask
  local f (Plus dict m n) = Plus dict (local f m) (local f n)
  local f (Ap dict g a) = Ap dict (local f g) (local f a)
  local f (Bind m k) = Bind (local f m) (local f . k)
  local f (Fix k) = Fix $ local f . k
  local f (Lift m) = Lift $ local f m
#if MIN_VERSION_mtl (2, 1, 0)
  reader = lift . reader
#endif

instance (MonadFix m, MonadState s m) => MonadState s (Perm m) where
  get = lift get
  put = lift . put
#if MIN_VERSION_mtl (2, 1, 0)
  state = lift . state
#endif

#ifdef LANGUAGE_DefaultSignatures
instance (MonadFix m, MonadThrow e m) => MonadThrow e (Perm m)
#else
instance (MonadFix m, MonadThrow e m) => MonadThrow e (Perm m) where
  throw = lift . throw
#endif

instance (MonadFix m, MonadPlus m, MonadWriter w m) => MonadWriter w (Perm m) where
  tell = lift . tell
  listen = lift . listen . sum1M
  pass = lift . pass . sum1M
#if MIN_VERSION_mtl (2, 1, 0)
  writer = lift . writer
#endif

infixr 6 <>
(<>) :: Perm m a -> Perm m a -> Perm m a
(<>) = Plus unit

mapFst :: (a -> a') -> (a, b) -> (a', b)
mapFst f (a, b) = (f a, b)
