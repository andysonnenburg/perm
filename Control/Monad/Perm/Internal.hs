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
       , hoistPerm
       ) where

import Control.Applicative
import Control.Monad
#if LANGUAGE_DefaultSignatures
import Control.Monad.Catch.Class (MonadThrow)
#else
import Control.Monad.Catch.Class (MonadThrow (throw))
#endif
import Control.Monad.Fix (fix)
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

import Prelude (($), (.), const, flip, id, snd)

-- | The permutation applicative
data Perm m a where
  Branch :: Branch m a -> Perm m a
  Plus :: PlusDict m -> Perm m a -> Perm m a -> Perm m a

data Branch m a where
  Ap :: FlipApDict m -> Perm m (a -> b) -> m a -> Branch m b
  Bind :: Monad m => m a -> (a -> Perm m b) -> Branch m b
  Lift :: m a -> Branch m a

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

type FlipApDict m = forall a b . m a -> m (a -> b) -> m b

applicative :: Applicative m => FlipApDict m
applicative = (<**>)

monad :: Monad m => FlipApDict m
monad a f = flip ($) `liftM` a `ap` f

-- | Unwrap a 'Perm', combining actions using the 'Alternative' for @f@.
sum1 :: Alternative m => Perm m a -> m a
sum1 m = runPerm m (<|>)

-- | Unwrap a 'Perm', combining actions using the 'MonadPlus' for @f@.
sum1M :: MonadPlus m => Perm m a -> m a
sum1M m = runPerm m mplus

runPerm :: Perm m b -> (forall a . m a -> m a -> m a) -> m b
runPerm (Branch m) plus = runBranch m plus
runPerm (Plus x m n) d = fromPlusDict d x (runPerm m d) (runPerm n d)

runBranch :: Branch m b -> (forall a . m a -> m a -> m a) -> m b
runBranch (Ap flipAp perm m) plus = m `flipAp` runPerm perm plus
runBranch (Bind m k) plus = m >>= \ a -> runPerm (k a) plus
runBranch (Lift m) _ = m

-- | A version of 'lift' that can be used without a 'Monad' for @m@.
liftPerm :: m a -> Perm m a
liftPerm = Branch . Lift

{- |
Lift a monad homomorphism from @m@ to @n@ into a monad homomorphism from
@'Perm' m@ to @'Perm' n@.
-}
hoistPerm :: Monad n => (forall a . m a -> n a) -> Perm m b -> Perm n b
hoistPerm f (Branch m) = Branch (hoistBranch f m)
hoistPerm f (Plus _ m n) = Plus unit (hoistPerm f m) (hoistPerm f n)

hoistBranch :: Monad n => (forall a . m a -> n a) -> Branch m b -> Branch n b
hoistBranch f (Ap _ perm m) = Ap monad (hoistPerm f perm) (f m)
hoistBranch f (Bind m k) = Bind (f m) (hoistPerm f . k)
hoistBranch f (Lift m) = Lift (f m)

instance Monoid (m a) => Monoid (Perm m a) where
  mappend = (<>)
  mempty = liftPerm mempty

instance Functor m => Functor (Perm m) where
  fmap f (Branch m) = Branch (fmap f m)
  fmap f (Plus dict m n) = Plus dict (fmap f m) (fmap f n)

instance Functor m => Functor (Branch m) where
  fmap f (Ap flipAp perm m) = Ap flipAp (fmap (f .) perm) m
  fmap f (Bind m k) = Bind m (fmap f . k)
  fmap f (Lift m) = Lift (fmap f m)

instance Applicative m => Applicative (Perm m) where
  pure = liftPerm . pure
  f <*> a = mapB (`apB` a) f <> mapB (f `apP`) a

apB :: Applicative m => Branch m (a -> b) -> Perm m a -> Branch m b
Ap flipAp perm m `apB` a = Ap flipAp (flipA2 perm a) m
Bind m k `apB` a = Bind m ((<*> a) . k)
Lift f `apB` a = Ap applicative (flip ($) <$> a) f

apP :: Applicative m => Perm m (a -> b) -> Branch m a -> Branch m b
f `apP` Ap flipAp perm m = Ap flipAp (f .@ perm) m
f `apP` Bind m k = Bind m ((f <*>) . k)
f `apP` Lift a = Ap (<**>) f a

flipA2 :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

(.@) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

instance Alternative m => Alternative (Perm m) where
  empty = liftPerm empty
  (<|>) = Plus alternative

instance Monad m => Monad (Perm m) where
  return = lift . return
  (>>=) = bind
  (>>) = then'
  fail = lift . fail

bind :: Monad m => Perm m a -> (a -> Perm m b) -> Perm m b
m `bind` k = mapB (`bindB` k) m <> mfix' (mapB (m `thenP`) . k)

bindB :: Monad m => Branch m a -> (a -> Perm m b) -> Branch m b
Ap _ perm m `bindB` k = Bind m (\ a -> k . ($ a) =<< perm)
Bind m f `bindB` g = Bind m (f >=> g)
Lift m `bindB` k = m `Bind` k

mfix' :: (a -> m b) -> m b
mfix' f = snd $ fix $ \ ~(a, _) -> (a, f a)

then' :: Monad m => Perm m a -> Perm m b -> Perm m b
m `then'` n = mapB (`thenB` n) m <> mapB (m `thenP`) n

thenB :: Monad m => Branch m a -> Perm m b -> Branch m b
Ap flipAp perm m `thenB` n = Ap flipAp (perm `then'` liftM' const n) m
Bind m k `thenB` n = Bind m ((`then'` n) . k)
Lift m `thenB` n = Ap monad (liftM' const n) m

thenP :: Monad m => Perm m a -> Branch m b -> Branch m b
m `thenP` Ap flipAp perm n = Ap flipAp (m `then'` perm) n
m `thenP` Bind n k = Bind n ((m `then'`) . k)
m `thenP` Lift n = Ap monad (liftM' (flip const) m) n

liftM' :: Monad m => (a -> b) -> Perm m a -> Perm m b
liftM' f (Branch m) = Branch (liftB f m)
liftM' f (Plus dict m n) = Plus dict (liftM' f m) (liftM' f n)

liftB :: Monad m => (a -> b) -> Branch m a -> Branch m b
liftB f (Ap flipAp perm m) = Ap flipAp (liftM' (f .) perm) m
liftB f (Bind m k) = Bind m (liftM' f . k)
liftB f (Lift m) = Lift (liftM f m)

instance MonadPlus m => MonadPlus (Perm m) where
  mzero = lift mzero
  mplus = Plus monadPlus

instance MonadTrans Perm where
  lift = Branch . Lift

instance MonadIO m => MonadIO (Perm m) where
  liftIO = lift . liftIO

instance MonadReader r m => MonadReader r (Perm m) where
  ask = lift ask
  local f = mapB (localBranch f)
#if MIN_VERSION_mtl(2, 1, 0)
  reader = lift . reader
#endif

localBranch :: MonadReader r m => (r -> r) -> Branch m a -> Branch m a
localBranch f (Ap dict perm m) = Ap dict (local f perm) (local f m)
localBranch f (Bind m k) = Bind (local f m) (local f . k)
localBranch f (Lift m) = Lift (local f m)

instance MonadState s m => MonadState s (Perm m) where
  get = lift get
  put = lift . put
#if MIN_VERSION_mtl(2, 1, 0)
  state = lift . state
#endif

#ifdef LANGUAGE_DefaultSignatures
instance MonadThrow e m => MonadThrow e (Perm m)
#else
instance MonadThrow e m => MonadThrow e (Perm m) where
  throw = lift . throw
#endif

mapB :: (Branch m a -> Branch m b) -> Perm m a -> Perm m b
mapB f (Branch m) = Branch (f m)
mapB f (Plus plus m n) = Plus plus (mapB f m) (mapB f n)

infixr 6 <>
(<>) :: Perm m a -> Perm m a -> Perm m a
(<>) = Plus unit

