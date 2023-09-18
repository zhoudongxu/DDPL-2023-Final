{-# LANGUAGE TemplateHaskell #-}

-- |

module Main where

-- |
import Data.Word (Word8)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH


import qualified Data.Map as M

import Gibbon.MyLocTypeLang.Syntax (Multiplicity(..))

-- import L0.Specialize
import LocTypeCheck.Typecheck
import LocTypeCheck.Interp

main :: IO ()
main = defaultMain allTests
  where allTests = testGroup "All"
                   [ locTypeCheckTypecheckerTests,
                     locInterpTests]



