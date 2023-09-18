{-# LANGUAGE TemplateHaskell #-}

-- | Tests for Interp
--
module LocTypeCheck.Interp
  (locInterpTests) where

import Test.Tasty.HUnit
import Test.Tasty.TH
import Test.Tasty

import Data.Map as M

import Gibbon.Common
import Gibbon.Language

import Gibbon.L1.Syntax as L1
import Gibbon.L1.Interp as L1
import Gibbon.MyLocTypeLang.Interp
import Gibbon.MyLocTypeLang.Helper 

p1 :: Prog1
p1 = Prog emptyDD M.empty
          (Just ( LetE ("x", [], IntTy, LitE 3) $
                  VarE "x"
                , IntTy ))

case_test1 :: Assertion
case_test1 = "3" @=? gInterpNoLogs () (RunConfig 1 1 dbgLvl False) p1

locInterpTests :: TestTree
locInterpTests = $(testGroupGenerator)