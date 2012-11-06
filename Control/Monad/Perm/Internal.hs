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
import Control.Monad
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

import Prelude (($), (.), const, flip, fst, id, snd, uncurry)

-- | The permutation applicative
data Perm m a where
  Branch :: Branch m a -> Perm m a
  Plus :: PlusDict m -> Perm m a -> Perm m a -> Perm m a

data Branch m a where
  Ap :: FlipApDict m -> Perm m (a -> b) -> m a -> Branch m b
  Bind :: Monad m => m a -> (a -> Perm m b) -> Branch m b
  Fix :: MonadFix m => (a -> b) -> (a -> Perm m a) -> Branch m b
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
runBranch (Fix f k) plus = liftM f $ mfix $ \ a -> runPerm (k a) plus
runBranch (Lift m) _ = m

-- | A version of 'lift' that can be used without a 'Monad' for @m@.
liftPerm :: m a -> Perm m a
liftPerm = Branch . Lift

liftPlus :: (forall a . m a -> m a -> m a) ->
            Perm m b -> Perm m b -> Perm m b
liftPlus plus = Plus (PlusDict (Just plus))

{- |
Lift a monad homomorphism from @m@ to @n@ into a monad homomorphism from
@'Perm' m@ to @'Perm' n@.
-}
hoistPerm :: MonadFix n => (forall a . m a -> n a) -> Perm m b -> Perm n b
hoistPerm f (Branch m) = Branch (hoistBranch f m)
hoistPerm f (Plus _ m n) = Plus unit (hoistPerm f m) (hoistPerm f n)

hoistBranch :: MonadFix n => (forall a . m a -> n a) -> Branch m b -> Branch n b
hoistBranch f (Ap _ perm m) = Ap monad (hoistPerm f perm) (f m)
hoistBranch f (Bind m k) = Bind (f m) (hoistPerm f . k)
hoistBranch f (Fix g k) = Fix g (hoistPerm f . k)
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
  fmap f (Fix g k) = Fix (f . g) k
  fmap f (Lift m) = Lift (fmap f m)

instance Applicative m => Applicative (Perm m) where
  pure = liftPerm . pure
  f <*> a = mapB (`apB` a) f <> mapB (f `apP`) a

apB :: Applicative m => Branch m (a -> b) -> Perm m a -> Branch m b
Ap flipAp perm m `apB` a = Ap flipAp (flipA2 perm a) m
Bind m k `apB` a = Bind m ((<*> a) . k)
Fix f k `apB` n = Fix (uncurry f) $ \ ~(a, _b) -> zipA (k a) n
Lift f `apB` a = Ap applicative (flip ($) <$> a) f

apP :: Applicative m => Perm m (a -> b) -> Branch m a -> Branch m b
f `apP` Ap flipAp perm m = Ap flipAp (f .@ perm) m
f `apP` Bind m k = Bind m ((f <*>) . k)
m `apP` Fix f k = Fix (\ (a, b) -> a (f b)) $ \ ~(_a, b) -> zipA m (k b)
f `apP` Lift a = Ap (<**>) f a

flipA2 :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

(.@) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

instance Alternative m => Alternative (Perm m) where
  empty = liftPerm empty
  (<|>) = Plus alternative

instance MonadFix m => Monad (Perm m) where
  return = lift . return
  (>>=) = bind
  (>>) = then'
  fail = lift . fail

bind :: MonadFix m => Perm m a -> (a -> Perm m b) -> Perm m b
m `bind` k = mapB (`bindB` k) m <> mapBindP m k

bindB :: MonadFix m => Branch m a -> (a -> Perm m b) -> Branch m b
Ap _ perm m `bindB` k = Bind m (\ a -> perm >>= k . ($ a))
Bind m f `bindB` g = Bind m (f >=> g)
Fix f k `bindB` k' = Fix snd (mapB (`bindB` \ a' -> liftM' ((,) a') . k' $ f a') . k . fst)
Lift m `bindB` k = Bind m k

mapBindP :: MonadFix m => Perm m a -> (a -> Perm m b) -> Perm m b
mapBindP m k = liftM' snd $ mfix' $ \ ~(a, _b) -> mapB (m `zipP`) $ k a

mfix' :: MonadFix m => (a -> Perm m a) -> Perm m a
mfix' = Branch . Fix id

then' :: Monad m => Perm m a -> Perm m b -> Perm m b
m `then'` n = mapB (`thenB` n) m <> mapB (m `thenP`) n

thenB :: Monad m => Branch m a -> Perm m b -> Branch m b
Ap flipAp perm m `thenB` n = Ap flipAp (perm `then'` liftM' const n) m
Bind m k `thenB` n = Bind m ((`then'` n) . k)
Fix _ k `thenB` n = Fix snd $ \ ~(a, _b) -> mapB (`zipB` n) (k a)
Lift m `thenB` n = Ap monad (liftM' const n) m

thenP :: Monad m => Perm m a -> Branch m b -> Branch m b
m `thenP` Ap flipAp perm n = Ap flipAp (m `then'` perm) n
m `thenP` Bind n k = Bind n ((m `then'`) . k)
m `thenP` Fix f k = Fix f $ \ a -> mapB (m `thenP`) (k a)
m `thenP` Lift n = Ap monad (liftM' (flip const) m) n

liftM' :: Monad m => (a -> b) -> Perm m a -> Perm m b
liftM' f (Branch m) = Branch (liftB f m)
liftM' f (Plus dict m n) = Plus dict (liftM' f m) (liftM' f n)

liftB :: Monad m => (a -> b) -> Branch m a -> Branch m b
liftB f (Ap flipAp perm m) = Ap flipAp (liftM' (f .) perm) m
liftB f (Bind m k) = Bind m (liftM' f . k)
liftB f (Fix g k) = Fix (f . g) k
liftB f (Lift m) = Lift (liftM f m)

zipM' :: Monad m => Perm m a -> Perm m b -> Perm m (a, b)
zipM' m n = mapB (`zipB` n) m <> mapB (m `zipP`) n

zipB :: Monad m => Branch m a -> Perm m b -> Branch m (a, b)
zipB (Ap flipAp perm m) n = Ap flipAp (liftM' apFst $ zipM' perm n) m
zipB (Bind m k) n = Bind m $ \ a -> zipM' (k a) n
zipB (Fix f k) n = Fix (mapFst f) $ \ ~(a, _b) -> mapB (`zipB` n) $ k a
zipB (Lift m) n = Ap monad (liftM' (flip (,)) n) m

zipP :: Monad m => Perm m a -> Branch m b -> Branch m (a, b)
zipP m (Ap flipAp perm n) = Ap flipAp (liftM' apSnd $ zipM' m perm) n
zipP m (Bind n k) = Bind n $ zipM' m . k
zipP m (Fix f k) = Fix (fmap f) $ \ ~(_a, b) -> mapB (m `zipP`) $ k b
zipP m (Lift n) = Ap monad (liftM' (,) m) n

instance (MonadFix m, MonadPlus m) => MonadPlus (Perm m) where
  mzero = lift mzero
  mplus = Plus monadPlus

instance MonadTrans Perm where
  lift = Branch . Lift

instance (MonadFix m, MonadIO m) => MonadIO (Perm m) where
  liftIO = lift . liftIO

instance (MonadFix m, MonadReader r m) => MonadReader r (Perm m) where
  ask = lift ask
  local f = mapB (localBranch f)
#if MIN_VERSION_mtl(2, 1, 0)
  reader = lift . reader
#endif

localBranch :: (MonadFix m, MonadReader r m) =>
               (r -> r) -> Branch m a -> Branch m a
localBranch f (Ap flipAp perm m) = Ap flipAp (local f perm) (local f m)
localBranch f (Bind m k) = Bind (local f m) (local f . k)
localBranch f (Fix g k) = Fix g $ local f . k
localBranch f (Lift m) = Lift $ local f m

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

mapB :: (Branch m a -> Branch m b) -> Perm m a -> Perm m b
mapB f (Branch m) = Branch $ f m
mapB f (Plus plus m n) = Plus plus (mapB f m) (mapB f n)

infixr 6 <>
(<>) :: Perm m a -> Perm m a -> Perm m a
(<>) = Plus unit

zipA :: Applicative m => m a -> m b -> m (a, b)
zipA m n = (,) <$> m <*> n

apFst :: (a -> a', b) -> a -> (a', b)
apFst (f, b) a = (f a, b)

apSnd :: (a, b -> b') -> b -> (a, b')
apSnd (a, f) b = (a, f b)

mapFst :: (a -> a') -> (a, b) -> (a', b)
mapFst f (a, b) = (f a, b)
