{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
module CoidealExample where

import Control.Comonad
import Control.Comonad.Coideal
import Numeric.Natural (Natural)

-- * The example coideal

-- | Example coideal comonad
data A x = Src x x | Tgt x
  deriving (Show, Eq, Functor)

instance Comonad A where
  extract (Src x _) = x
  extract (Tgt x) = x

  duplicate ax@(Src _ x1) = Src ax (Tgt x1)
  duplicate ax@(Tgt _) = Tgt ax

-- | the only one nontrivial cokleisli arrow
advance :: A x -> x
advance ax = case ax of
  Src _ x' -> x'
  Tgt x -> x

-- Accumulating store
data Accum x = Accum Natural (Natural -> x)
  deriving Functor

instance Comonad Accum where
  extract (Accum _ f) = f 0
  duplicate (Accum n f) = Accum n $ \m1 -> Accum (n + m1) (\m2 -> f (m1 + m2))

data Accum' x = Accum' Natural (Natural -> x)
  deriving Functor

fromAccum' :: Coideal Accum' x -> Accum x
fromAccum' wx' = case runCoideal wx' of
  (x, Accum' n f) -> Accum n (\m -> if m == 0 then x else f (m - 1))

toAccum' :: Accum x -> Coideal Accum' x
toAccum' (Accum n f) = Coideal (f 0, Accum' n (\m -> f (m + 1)))

instance ComonadCoideal Accum' where
  coidealExtend k (Accum' n f) = Accum' n $ \m1 -> k (toAccum' $ Accum (n + 1 + m1) (\m2 -> f (m1 + m2)))

-- | Comonad morphism to A.
nextMultipleOf :: Natural -> Accum x -> A x
nextMultipleOf d (Accum n f) = case n `mod` d of
  0 -> Tgt (f 0)
  r -> Src (f 0) (f (d - r))

-- | ComonadIdeal morphism to A'
nextMultipleOf' :: Natural -> Accum' x -> A' x
nextMultipleOf' d (Accum' n f) = case n `mod` d of
  0 -> Tgt'
  r -> Src' (f (d - r - 1))

-- | The coideal part of A
data A' x = Src' x | Tgt'
  deriving (Show, Eq, Functor)

instance ComonadCoideal A' where
  coidealExtend f (Src' x) = Src' (f $ Coideal (x, Tgt'))
  coidealExtend _ Tgt' = Tgt'

fromA' :: Coideal A' x -> A x
fromA' ax' = case runCoideal ax' of
  (x, Src' x') -> Src x x'
  (x, Tgt') -> Tgt x

toA' :: A x -> Coideal A' x
toA' (Src x x') = Coideal (x, Src' x')
toA' (Tgt x) = Coideal (x, Tgt')
