-- | <http://www.reddit.com/r/haskell/comments/12kuvr/permutation_monad_using_monadfix/>
module Main (main) where

import Control.Monad.Perm
import Control.Monad.Writer

import Test.Framework (Test, defaultMain)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assert)

redditExample1 :: Assertion
redditExample1 =
  assert $
  (execWriterT $ runPerm $ lift (tell "a") >>= \ _ -> lift (tell "b") >>= \ _ -> lift (tell "c"))
  ==
  ["abc", "acb", "bac", "bca", "cab", "cba"]

redditExample2 :: Assertion
redditExample2 =
  assert $
  (execWriterT $ runPerm $ lift (tell "a" >> return "b") >>= \ a -> lift (tell a) >>= \ _ -> lift (tell "c"))
  ==
  ["abc", "acb", "bac", "bca", "cab", "cba"]

tests :: [Test]
tests =
  [ testCase "redditExample1" redditExample1
  , testCase "redditExample2" redditExample2
  ]

main :: IO ()
main = defaultMain tests
