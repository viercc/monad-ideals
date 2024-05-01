{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# LANGUAGE TypeOperators #-}
module Main (main) where

import System.IO (stderr, hPutStrLn)
import System.Exit (exitFailure)

import Data.Char (toUpper)
import Data.Foldable (toList)
import Data.Proxy
import Data.Semigroup (Min(..))

import Data.List.NonEmpty (NonEmpty(..))

import Control.Monad.Isolated
import Control.Monad.Ideal
import Data.Functor.KeepLeft
import Data.List.TwoOrMore
import Data.List.NotOne
import Control.Monad.Coproduct

putErr :: String -> IO ()
putErr = hPutStrLn stderr

(===) :: (Show a, Eq a) => a -> a -> String -> IO ()
(===) x y name = if x == y then pure () else putErr errMsg >> exitFailure
  where
    sx = show x
    sy = show y
    errMsg = "failure: " ++ name ++ "\n\t" ++ sx ++ " =/= " ++ sy

infix 1 ===

item :: String -> (String -> IO ()) -> IO ()
item = flip ($)

main :: IO ()
main = do
  testsIsolated
  testsIdeal
  testsKeepLeft
  testsTwoOrMore
  testsNotOne
  testsCoproduct
  --testsCoideal

testsIsolated :: IO ()
testsIsolated = do
  -- Unite
  item "fmapUnite" $ fmap @(Unite []) succ (Unite (Left 1)) === Unite (Left 2)
  item "fmapUnite" $ fmap @(Unite []) succ (Unite (Right [1,1])) === Unite (Right [2,2])
  item "toListUnite" $ toList (Unite (Left 'a')) === ['a']
  item "hoistUnite" $ hoistUnite toList (Unite (Left 'a')) === (Unite (Left 'a'))
  item "hoistUnite" $ hoistUnite toList (Unite (Right Nothing)) === Unite (Right [])

  item "Isolated Proxy" $
    (Proxy `impureBind` pure) === Unite (Right Proxy)
  item "Isolated ((,) s)" $
    ((Min 1, 2) `impureBind` \x -> Unite (Right (Min x, x + 1)))
      ===
    Unite (Right (Min 1, 3))

testsIdeal :: IO ()
testsIdeal = do
  item "MonadIdeal ((,) s)" $
    ((Min 1, 2) `idealBind` pure) === (Min 1, 2)
  item "MonadIdeal ((,) s)" $
    ((Min 1, 2) `idealBind` \x -> (ideal . Right) (Min 0, x + 1))
      ===
    (Min 0, 3)

testsKeepLeft :: IO ()
testsKeepLeft = do
  item "Semigroup (KeepLeft c)" $ KeepLeft 1 <> KeepLeft 5 === KeepLeft 1
  item "Semigroup (KeepLeft c)" $ KeepLeft 1 <> KeepLeft 6 === KeepLeft 1
  item "Semigroup (KeepLeft c)" $ KeepLeft 2 <> KeepLeft 5 === KeepLeft 2
  item "Semigroup (KeepLeft c)" $ KeepLeft 2 <> KeepLeft 6 === KeepLeft 2
  
  item "MonadIdeal (KeepLeft c)" $
    (KeepLeft 1 `idealBind` pure) === KeepLeft 1
  item "MonadIdeal (KeepLeft c)" $
    (KeepLeft 1 `idealBind` \a -> ideal . Right $ KeepLeft (10 + a)) === KeepLeft 1

testsTwoOrMore :: IO ()
testsTwoOrMore = do
  item "twoOrMore" $ twoOrMore ("a" :| []) === Left "a"
  item "twoOrMore" $ twoOrMore ("a" :| ["b", "c"]) === Right (TwoOrMore "a" "b" ["c"])

  let abc = TwoOrMore 'a' 'b' ['c']

  item "MonadIdeal TwoOrMore" $
    (abc `idealBind` \x -> pure (toUpper x)) === TwoOrMore 'A' 'B' ['C']
  item "MonadIdeal TwoOrMore" $
    (abc `idealBind` \x -> ideal . Right $ TwoOrMore x x [x, x]) === TwoOrMore 'a' 'a' "aabbbbcccc"
  
testsNotOne :: IO ()
testsNotOne = do
  item "notOne" $ notOne "" === Right Zero
  item "notOne" $ notOne "a" === Left 'a'
  item "notOne" $ notOne "abcd" === Right (Multiple $ TwoOrMore 'a' 'b' "cd")

  let abc = Multiple $ TwoOrMore 'a' 'b' ['c']
      empty' = Zero
      quadruple x = Multiple $ TwoOrMore x x [x, x]

  item "Isolated NotOne" $
    (abc `impureBind` \x -> pure (toUpper x)) === Unite (Right (fmap toUpper abc))
  item "Isolated NotOne" $
    (abc `impureBind` \x -> if x == 'a' then pure 'M' else Unite (Right empty')) === pure 'M'
  item "Isolated NotOne" $
    (abc `impureBind` \x -> Unite . Right $ quadruple x)
      ===
    (Unite . Right . Multiple $ TwoOrMore 'a' 'a' "aabbbbcccc")

impure :: f a -> Unite f a
impure = Unite . Right

injectMonad1 :: Functor m0 => Unite m0 a -> Unite (m0 :+ n0) a
injectMonad1 = hoistUnite inject1

injectMonad2 :: Functor n0 => Unite n0 a -> Unite (m0 :+ n0) a
injectMonad2 = hoistUnite inject2

testsCoproduct :: IO ()
testsCoproduct = do
  let abc = Multiple $ TwoOrMore 'a' 'b' ['c']
      double x = Multiple $ TwoOrMore x x [] 
      quadruple x = Multiple $ TwoOrMore x x [x, x]
      abc' = TwoOrMore 'a' 'b' ['c']
  item "Coproduct-inject1-inject1" $
    let m1 :: Unite (NotOne :+ NotOne) Char
        m1 = do
          x <- injectMonad1 $ impure abc
          injectMonad1 $ impure (quadruple x)
        m2 = injectMonad1 $ impure abc >>= impure . quadruple
    in m1 === m2
  item "Coproduct-inject2-inject2" $
    let m1 :: Unite (NotOne :+ NotOne) Char
        m1 = do
          x <- injectMonad2 $ impure abc
          injectMonad2 $ impure (quadruple x)
        m2 = injectMonad2 $ impure abc >>= impure . quadruple
    in m1 === m2
  
  item "Coproduct-collapse" $
    let m1 :: Unite (NotOne :+ NotOne) Char
        m1 = do
          x <- injectMonad1 $ impure abc
          y <- injectMonad2 $ impure abc
          injectMonad2 $ if x == y then pure () else impure Zero
          pure y
        m2 = injectMonad1 $ impure abc
    in m1 === m2
  
  item "Coproduct-eitherMonad" $
    let m1 :: [Char]
        m1 = either pure (eitherMonad toList toList) . runUnite $ do
          x <- injectMonad1 $ impure abc
          y <- if x == 'a' then injectMonad2 (impure abc) else injectMonad1 (impure abc)
          if y == 'b' then injectMonad2 (impure (double y)) else pure y
        m2 = "abbcabbcabbc"
    in m1 === m2
  
  let f :: Char -> Ideal (TwoOrMore :+ TwoOrMore) Char
      f 'a' = ideal . Right $ inject1 (TwoOrMore 'A' 'A' [])
      f 'b' = ideal . Right $ inject2 (TwoOrMore 'B' 'B' [])
      f c   = ideal . Left $ c
  
  item "Coproduct-idealBind" $
    let m1 :: (TwoOrMore :+ TwoOrMore) Char
        m1 = inject1 abc' `idealBind` f
        
        m2 :: (TwoOrMore :+ TwoOrMore) Char
        m2 = Coproduct $ Left $ Mutual $
          TwoOrMore
            (Left 'A')
            (Left 'A')
            [
              Right (Mutual $ TwoOrMore (Left 'B') (Left 'B') [])
            , Left 'c'
            ]
    in m1 === m2
  
  item "Coproduct-||||" $
    let m1 = id |||| id $ inject1 abc' `idealBind` f
        m2 = TwoOrMore 'A' 'A' ['B', 'B', 'c']
    in m1 === m2