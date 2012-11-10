-- | <http://www.reddit.com/r/haskell/comments/12kuvr/permutation_monad_using_monadfix/>
module Main (main) where

import Control.Applicative
import Control.Monad.Perm
import Control.Monad.Writer

import Test.Framework (Test, defaultMain)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, (@=?))

redditExample1 :: Assertion
redditExample1 =
  ["abc", "acb", "bac", "bca", "cab", "cba"]
  @=?
  (execWriterT $ runPerm $ lift (tell "a") >>= \ _ -> lift (tell "b") >>= \ _ -> lift (tell "c"))

redditExample1UsingThen :: Assertion
redditExample1UsingThen =
  ["abc", "acb", "bac", "bca", "cab", "cba"]
  @=?
  (execWriterT $ runPerm $ lift (tell "a") >> lift (tell "b") >> lift (tell "c"))

redditExample1UsingAp :: Assertion
redditExample1UsingAp =
  ["abc", "acb", "bac", "bca", "cab", "cba"]
  @=?
  (execWriterT $ runPerm $ lift (tell "a") *> lift (tell "b") *> lift (tell "c"))

redditExample2 :: Assertion
redditExample2 =
  ["abc", "acb", "bac", "bca", "cab", "cba"]
  @=?
  (execWriterT $ runPerm $ lift (tell "a" >> return "b") >>= \ a -> lift (tell a) >>= \ _ -> lift (tell "c"))

tests :: [Test]
tests =
  [ testCase "redditExample1" redditExample1
  , testCase "redditExample1UsingThen" redditExample1UsingThen
  , testCase "reddit1ExampleUsingAp" redditExample1UsingAp
  , testCase "redditExample2" redditExample2
  ]

main :: IO ()
main = defaultMain tests
