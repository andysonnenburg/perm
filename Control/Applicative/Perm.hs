{-# LANGUAGE
    ExistentialQuantification
  , Rank2Types #-}
{- |
License: BSD-style (see the file LICENSE)
Maintainer: Andy Sonnenburg <andy22286@gmail.com>
Stability: experimental
Portability: non-portable
-}
module Control.Applicative.Perm
       ( PermT
       , runPermT
       , runPermT'
       , liftPerm
       , hoistPerm
       ) where

import Control.Applicative
import Control.Monad (MonadPlus (mplus, mzero), ap, liftM, return)
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Foldable (foldr)
import Data.Functor (Functor (fmap))
import Data.Monoid (mappend, mempty)

import Prelude (Maybe (..), ($), (.), flip, id, maybe)

data PermT m a = Choice (Maybe a) [Branch m a]

data Branch m b = forall a . Branch (PermT m (a -> b)) (m a)

instance Functor (PermT m) where
  fmap f (Choice a xs) = Choice (f <$> a) (fmap f <$> xs)

instance Functor (Branch m) where
  fmap f (Branch perm m) = Branch (fmap (f .) perm) m

instance Applicative (PermT m) where
  pure a = Choice (pure a) mempty
  f@(Choice f' fs) <*> a@(Choice a' as) =
    Choice (f' <*> a') (fmap (`apB` a) fs `mappend` fmap (f `apP`) as)

instance Alternative (PermT m) where
  empty = Choice empty mempty
  m@(Choice (Just _) _) <|> _ = m
  Choice Nothing xs <|> Choice b ys = Choice b (xs `mappend` ys)

instance MonadTrans PermT where
  lift = liftPerm

apP :: PermT m (a -> b) -> Branch m a -> Branch m b
apP f (Branch perm m) = Branch (f .@ perm) m

(.@) :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
(.@) = liftA2 (.)

apB :: Branch m (a -> b) -> PermT m a -> Branch m b
apB (Branch perm m) a = Branch (flipA2 perm a) m

flipA2 :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
flipA2 = liftA2 flip

runPermT :: Alternative m => PermT m a -> m a
runPermT = lower
  where
    lower (Choice a xs) = foldr ((<|>) . f) (maybe empty pure a) xs
    f (Branch perm m) = m <**> runPermT perm

runPermT' :: MonadPlus m => PermT m a -> m a
runPermT' = lower
  where
    lower (Choice a xs) = foldr (mplus . f) (maybe mzero return a) xs
    f (Branch perm m) = flip ($) `liftM` m `ap` runPermT' perm

liftPerm :: m a -> PermT m a
liftPerm = Choice empty . pure . liftBranch

liftBranch :: m a -> Branch m a
liftBranch = Branch (Choice (pure id) mempty)

hoistPerm :: (forall a . m a -> n a) -> PermT m b -> PermT n b
hoistPerm f (Choice a xs) = Choice a (hoistBranch f <$> xs)

hoistBranch :: (forall a . m a -> n a) -> Branch m b -> Branch n b
hoistBranch f (Branch perm m) = Branch (hoistPerm f perm) (f m)
