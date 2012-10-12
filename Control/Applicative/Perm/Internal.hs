{-# LANGUAGE CPP #-}
#ifdef LANGUAGE_DataKinds
{-# LANGUAGE DataKinds #-}
#else
{-# LANGUAGE EmptyDataDecls #-}
#endif
{-# LANGUAGE
    ExistentialQuantification
  , FlexibleInstances
  , GADTs
  , Rank2Types #-}
{- |
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Applicative.Perm.Internal
       ( PermT
#ifdef LANGUAGE_DataKinds
       , Constraint (..)
#else
       , Alternative
       , MonadPlus
#endif
       , runApplicativePermT
       , runMonadPermT
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative hiding (Alternative)
import qualified Control.Applicative as Applicative (Alternative)
import Control.Monad hiding (MonadPlus)
import qualified Control.Monad as Monad (MonadPlus)
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Foldable (foldr)
import Data.Monoid (mappend, mempty)

import Prelude (Maybe (..), ($), (.), const, flip, id, map, maybe)

data PermT c m a = Choice (Maybe a) [Branch c m a]

#ifdef LANGUAGE_DataKinds
data Constraint
  = Alternative
  | MonadPlus
#else
data Alternative
data MonadPlus
#endif

data Branch c m b where
  Ap :: PermT c m (a -> b) -> m a -> Branch c m b
  Bind :: (a -> PermT MonadPlus m b) -> m a -> Branch MonadPlus m b

instance Functor (PermT c m) where
  fmap f (Choice a xs) = Choice (f <$> a) (fmap f <$> xs)

instance Functor (Branch c m) where
  fmap f (Ap perm m) = Ap (fmap (f .) perm) m
  fmap f (Bind k m) = Bind (fmap f . k) m

instance Applicative (PermT c m) where
  pure a = Choice (pure a) mempty
  f@(Choice f' fs) <*> a@(Choice a' as) =
    Choice (f' <*> a') (fmap (`apB` a) fs `mappend` fmap (f `apP`) as)

instance Applicative.Alternative (PermT c m) where
  empty = Choice empty mempty
  m@(Choice (Just _) _) <|> _ = m
  Choice Nothing xs <|> Choice b ys = Choice b (xs `mappend` ys)

instance Monad (PermT MonadPlus m) where
  return a = Choice (return a) mempty
  Choice Nothing ms >>= k = Choice Nothing (map (bindP k) ms)
  Choice (Just a) ms >>= k = case k a of
    Choice a' ms' -> Choice a' (map (bindP k) ms `mappend` ms')
  m@(Choice m' ms) >> n@(Choice n' ns) =
    Choice (m' >> n') (map (`thenB` n) ms `mappend` map (m `thenP`) ns)
  fail _ = Choice mzero mempty

instance Monad.MonadPlus (PermT MonadPlus m) where
  mzero = Choice mzero mempty
  m@(Choice (Just _) _) `mplus` _ = m
  Choice Nothing xs `mplus` Choice b ys = Choice b (xs `mappend` ys)

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

bindP :: (a -> PermT MonadPlus m b) -> Branch MonadPlus m a -> Branch MonadPlus m b
bindP k (Ap perm m) = Bind (\ a -> perm >>= k . ($ a)) m
bindP k (Bind k' m) = Bind (k' >=> k) m

thenP :: PermT c m a -> Branch c m b -> Branch c m b
m `thenP` Ap perm m' = (m *> perm) `Ap` m'
m `thenP` Bind k m' = Bind ((m >>) . k) m'

thenB :: Branch c m a -> PermT c m b -> Branch c m b
Ap perm m `thenB` n = (perm *> fmap const n) `Ap` m
Bind k m `thenB` n = Bind ((>> n) . k) m

runApplicativePermT :: Applicative.Alternative m => PermT Alternative m a -> m a
runApplicativePermT = lower
  where
    lower (Choice a xs) = foldr ((<|>) . f) (maybe empty pure a) xs
    f (perm `Ap` m) = m <**> runApplicativePermT perm

runMonadPermT :: Monad.MonadPlus m => PermT MonadPlus m a -> m a
runMonadPermT = lower
  where
    lower (Choice a xs) = foldr (mplus . f) (maybe mzero return a) xs
    f (perm `Ap` m) = flip ($) `liftM` m `ap` runMonadPermT perm
    f (Bind k m) = m >>= runMonadPermT . k

-- | A version of 'lift' without the @MonadPlus' m@ constraint
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
