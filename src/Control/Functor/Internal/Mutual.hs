{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Functor.Internal.Mutual
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
module Control.Functor.Internal.Mutual where

import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable

newtype Mutual p m n a = Mutual {runMutual :: m (p a (Mutual p n m a))}

deriving instance (Eq (m (p a (Mutual p n m a))), Eq (n (p a (Mutual p m n a)))) => Eq (Mutual p n m a)
deriving instance (Show (m (p a (Mutual p n m a))), Show (n (p a (Mutual p m n a)))) => Show (Mutual p n m a)

instance (Bifunctor p, Functor m, Functor n) => Functor (Mutual p m n) where
  fmap f = Mutual . fmap (bimap f (fmap f)) . runMutual

instance (Bifoldable p, Foldable m, Foldable n) => Foldable (Mutual p m n) where
  foldMap f = foldMap (bifoldMap f (foldMap f)) . runMutual

instance (Bitraversable p, Traversable m, Traversable n) => Traversable (Mutual p m n) where
  traverse f = fmap Mutual . traverse (bitraverse f (traverse f)) . runMutual

foldMutual
  :: Bifunctor p
  => (forall a b. t a -> (a -> p b (t b)) -> t b)
  -> (forall a. m a -> t a)
  -> (forall a. n a -> t a)
  -> Mutual p m n c -> t c
foldMutual bind mt nt = (`bind` second (foldMutual bind nt mt)) . mt . runMutual

unfoldMutual
  :: Bifunctor p
  => (forall a b. (p a (s a) -> b) -> s a -> s b)
  -> (forall a. s a -> w a)
  -> (forall a. s a -> v a)
  -> s c -> Mutual p w v c
unfoldMutual ext sw sv = Mutual . sw . ext (second (unfoldMutual ext sv sw))
