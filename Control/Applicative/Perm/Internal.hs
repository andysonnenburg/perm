{-# LANGUAGE
    ExistentialQuantification
  , FlexibleInstances
  , GADTs
  , Rank2Types #-}
{- |
Copyright: Andy Sonnenburg (c) 2012
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Applicative.Perm.Internal
       ( PermT
       , runApplicativePermT
       , runMonadPermT
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Foldable (foldr)
import Data.Monoid ((<>), mempty)

import Prelude (Maybe (..), ($), (.), const, flip, id, map, maybe)

data PermT c m a = Choice (Maybe a) [Branch c m a]

data Branch c m b where
  Ap :: PermT c m (a -> b) -> m a -> Branch c m b
  Bind :: (a -> PermT Monad m b) -> m a -> Branch Monad m b

instance Functor (PermT c m) where
  fmap f (Choice a xs) = Choice (f <$> a) (fmap f <$> xs)

instance Functor (Branch c m) where
  fmap f (Ap perm m) = Ap (fmap (f .) perm) m
  fmap f (Bind k m) = Bind (fmap f . k) m

instance Applicative (PermT c m) where
  pure a = Choice (pure a) mempty
  f@(Choice f' fs) <*> a@(Choice a' as) =
    Choice (f' <*> a') (fmap (`apB` a) fs <> fmap (f `apP`) as)
  (*>) = then' (*>)

instance Alternative (PermT c m) where
  empty = zero empty
  (<|>) = plus

instance Monad (PermT Monad m) where
  return a = Choice (return a) mempty
  Choice Nothing ms >>= k = Choice Nothing (map (bindP k) ms)
  Choice (Just a) ms >>= k = case k a of
    Choice a' ms' -> Choice a' (map (bindP k) ms <> ms')
  (>>) = then' (>>)
  fail _ = Choice mzero mempty

instance MonadPlus (PermT Monad m) where
  mzero = zero mzero
  mplus = plus

instance MonadTrans (PermT c) where
  lift = liftPerm

apP :: PermT c m (a -> b) -> Branch c m a -> Branch c m b
f `apP` Ap perm m = (f .@ perm) `Ap` m
f `apP` Bind k m = Bind ((f `ap`) . k) m

(.@) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

apB :: Branch c m (a -> b) -> PermT c m a -> Branch c m b
Ap perm m `apB` a = flipA2 perm a `Ap` m
Bind k m `apB` a = Bind ((`ap` a) . k) m

flipA2 :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

bindP :: (a -> PermT Monad m b) -> Branch Monad m a -> Branch Monad m b
bindP k (Ap perm m) = Bind (\ a -> perm >>= k . ($ a)) m
bindP k (Bind k' m) = Bind (k' >=> k) m

then' :: (Maybe a -> Maybe b -> Maybe b) ->
         PermT c m a -> PermT c m b -> PermT c m b
then' thenMaybe m@(Choice m' ms) n@(Choice n' ns) =
  Choice (m' `thenMaybe` n') (map (`thenB` n) ms <> map (m `thenP`) ns)

thenP :: PermT c m a -> Branch c m b -> Branch c m b
m `thenP` Ap perm m' = (m *> perm) `Ap` m'
m `thenP` Bind k m' = Bind ((m >>) . k) m'

thenB :: Branch c m a -> PermT c m b -> Branch c m b
Ap perm m `thenB` n = (perm *> fmap const n) `Ap` m
Bind k m `thenB` n = Bind ((>> n) . k) m

zero :: Maybe a -> PermT c m a
zero zeroMaybe = Choice zeroMaybe mempty

plus :: PermT c m a -> PermT c m a -> PermT c m a
m@(Choice (Just _) _) `plus` _ = m
Choice Nothing xs `plus` Choice b ys = Choice b (xs <> ys)

runApplicativePermT :: Alternative m => PermT Applicative m a -> m a
runApplicativePermT = lower
  where
    lower (Choice a xs) = foldr ((<|>) . f) (maybe empty pure a) xs
    f (perm `Ap` m) = m <**> runApplicativePermT perm

runMonadPermT :: MonadPlus m => PermT Monad m a -> m a
runMonadPermT = lower
  where
    lower (Choice a xs) = foldr (mplus . f) (maybe mzero return a) xs
    f (perm `Ap` m) = flip ($) `liftM` m `ap` runMonadPermT perm
    f (Bind k m) = m >>= runMonadPermT . k

-- | A version of 'lift' without the @'Monad' m@ constraint
liftPerm :: m a -> PermT c m a
liftPerm = Choice empty . pure . liftBranch

liftBranch :: m a -> Branch c m a
liftBranch = Ap (Choice (pure id) mempty)

{- |
Lift a natural transformation from @m@ to @n@ into a natural transformation
from @'PermT' m@ to @'PermT' n@.
-}
hoistPerm :: (forall a . m a -> n a) -> PermT c m b -> PermT c n b
hoistPerm f (Choice a xs) = Choice a (hoistBranch f <$> xs)

hoistBranch :: (forall a . m a -> n a) -> Branch c m b -> Branch c n b
hoistBranch f (perm `Ap` m) = hoistPerm f perm `Ap` f m
hoistBranch f (Bind k m) = Bind (hoistPerm f . k) (f m)
