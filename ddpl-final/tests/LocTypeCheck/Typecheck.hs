{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}


module LocTypeCheck.Typecheck where

import Test.Tasty.HUnit
import Test.Tasty.TH
import Test.Tasty

import Control.Monad.Except
import Data.Map as M
import Data.Set as S

import Gibbon.Common hiding (FunDef)
import Gibbon.MyLocTypeLang.Syntax as L2
import Gibbon.MyLocTypeLang.Typecheck
import Gibbon.MyLocTypeLang.Helper
import Gibbon.L1.Syntax as L1

--

type Exp = Exp2

-- | Run the typechecker for (Prog {ddefs = Tree, fundefs = [add1], mainExp = exp})
--
tester :: Exp -> Either TCError (Ty2, LocationTypeState)
tester = runExcept . (tcExp ddfs env funs constrs regs tstate)
  where
    ddfs    = ddtree
    env     = Env2 M.empty M.empty
    funs    = M.empty
    constrs = ConstraintSet S.empty
    regs    = RegionSet S.empty
    tstate  = LocationTypeState M.empty


-- |
assertValue :: Exp -> (Ty2, LocationTypeState) -> Assertion
assertValue exp expected =
  case tester exp of
    Left err -> assertFailure $ show err
    Right actual -> expected @=? actual


-- |
assertError :: Exp -> TCError -> Assertion
assertError exp expected =
  case tester exp of
    Left actual -> expected @=? actual
    Right err -> assertFailure $ show err


-- Tests

case_test1 :: Assertion
case_test1 = assertValue exp (IntTy,LocationTypeState {tsmap = M.fromList []})
  where exp = LitE 1


case_test2 :: Assertion
case_test2 =  assertValue exp (IntTy,LocationTypeState {tsmap = M.fromList []})
  where exp = LetE ("a",[],IntTy, LitE 1)
                        (PrimAppE L1.AddP [VarE "a",
                                                     VarE "a"])

-- LetRegion r in 
--   LetLoc l = StartOf r in 1
case_test3 :: Assertion
case_test3 =  assertValue exp (IntTy,LocationTypeState {tsmap = M.fromList []})
  where exp = Ext $ LetRegionE (VarR "r") Undefined Nothing $
                              Ext $ LetLocE "l" (StartOfLE (VarR "r")) $
                              LitE 1

-- letregion r in
--   letloc l = startof r in
--     let throwaway = Leaf 1 in
--       2
case_test4 :: Assertion
case_test4 =  assertValue exp (IntTy,LocationTypeState {tsmap = M.fromList []})
  where exp = Ext $ LetRegionE (VarR "r") Undefined Nothing $
                              Ext $ LetLocE "l" (StartOfLE (VarR "r")) $
                              LetE ("throwaway", [],
                                              PackedTy "Tree" "l",
                                              DataConE "l" "Leaf" [LitE 1]) $
                              LitE 2

--unkonwn region case
-- letregion r in
--   letloc l = startof r1 in
--     let throwaway = Leaf l 1 in
--       2
case_test4_error1 :: Assertion
case_test4_error1 =  assertError exp expected
  where exp = Ext $ LetRegionE (VarR "r") Undefined Nothing $
              Ext $ LetLocE "l" (StartOfLE (VarR "r1")) $
              LetE ("throwaway", [], PackedTy "Tree" "l",
                              DataConE "l" "Leaf" [LitE 1]) $
               LitE 2

        expected = GenericTC "Region VarR (Var \"r1\") not in scope" (Ext (LetLocE (Var "l") (StartOfLE (VarR (Var "r1"))) (LetE (Var "throwaway",[],PackedTy "Tree" (Var "l"), DataConE (Var "l") "Leaf" [LitE 1]) (LitE 2))))

-- unknown location case
-- letregion r in
--   letloc l = startof r in
--     let throwaway = Leaf l1 1 in
--       2
case_test4_error2 :: Assertion
case_test4_error2 =  assertError exp expected
  where exp = Ext $ LetRegionE (VarR "r") Undefined Nothing $
              Ext $ LetLocE "l" (StartOfLE (VarR "r")) $
              LetE ("throwaway", [], PackedTy "Tree" "l1",
                              DataConE "l1" "Leaf" [LitE 1]) $
              LitE 2

        expected = GenericTC "Unknown location Var \"l1\"" (DataConE (Var "l1") "Leaf" [LitE 1])

-- letregion r in
--   letloc l = startof r in
--      letloc l1 = l + 1 in
--        let x = Leaf l1 1 in
--             letloc l2 = l1 + 1 in
--              let y = Leaf l2 2 in
--                let z = Node x y 1 in
--                   1
case_test5 :: Assertion
case_test5 =  assertValue exp (IntTy,LocationTypeState {tsmap = M.fromList []})
  where exp = Ext $ LetRegionE (VarR "r") Undefined Nothing $
              Ext $ LetLocE "l" (StartOfLE (VarR "r")) $
              Ext $ LetLocE "l1" (AfterConstantLE 1 "l") $
              LetE ("x", [], PackedTy "Tree" "l1", DataConE "l1" "Leaf" [LitE 1]) $
              Ext $ LetLocE "l2" (AfterVariableLE "x" "l1" False) $
              LetE ("y", [], PackedTy "Tree" "l2", DataConE "l2" "Leaf" [LitE 2]) $
              LetE ("z", [], PackedTy "Tree" "l", DataConE "l" "Node" [VarE "x", VarE "y"]) $
              LitE 1

-- filed order case
-- letregion r in
--   letloc l = startof r in
--      letloc l1 = l + 1 in
--        let x = Leaf l1 1 in
--             letloc l2 = l1 + 1 in
--              let y = Leaf l2 2 in
--                let z = Node y x 1 in
--                   1
case_test5_error1 :: Assertion
case_test5_error1 =  assertError exp expected
  where exp = Ext $ LetRegionE (VarR "r") Undefined Nothing $
              Ext $ LetLocE "l" (StartOfLE (VarR "r")) $
              Ext $ LetLocE "l1" (AfterConstantLE 1 "l") $
              LetE ("x", [], PackedTy "Tree" "l1",
                              DataConE "l1" "Leaf" [LitE 1]) $
              Ext $ LetLocE "l2" (AfterVariableLE "x" "l1" False) $
              LetE ("y", [], PackedTy "Tree" "l2",
                              DataConE "l2" "Leaf" [LitE 2]) $
              LetE ("z", [], PackedTy "Tree" "l",
                              DataConE "l" "Node"
                              [VarE "y", VarE "x"]) $
              LitE 1

        expected = LocationTC "Expected after constant relationship" (DataConE (Var "l") "Node" [VarE (Var "y"),VarE (Var "x")]) (Var "l") (Var "l2")

--  Pattern Matching case
-- letregion r in
--   letloc l = startof r in
--      letloc l1 = l + 1 in
--        let x = Leaf l1 1 in
--             letloc l2 = l1 + 1 in
--              let y = Leaf l2 2 in
--                let z = Node x y 1 in
--                   case z of
--                     [Leaf num:Int@lnum , node x:Tree@lnodex y:Tree@lnodey 0] 
case_test6 :: Assertion
case_test6 =  assertValue exp (IntTy,LocationTypeState {tsmap = M.fromList []})
  where exp = Ext $ LetRegionE (VarR "r") Undefined Nothing $
              Ext $ LetLocE "l" (StartOfLE (VarR "r")) $
              Ext $ LetLocE "l1" (AfterConstantLE 1 "l") $
              LetE ("x", [], PackedTy "Tree" "l1",
                              DataConE "l1" "Leaf" [LitE 1]) $
              Ext $ LetLocE "l2" (AfterVariableLE "x" "l1" False) $
              LetE ("y", [], PackedTy "Tree" "l2",
                              DataConE "l2" "Leaf" [LitE 2]) $
              LetE ("z", [], PackedTy "Tree" "l",
                              DataConE "l" "Node" [VarE "x",
                                                             VarE "y"]) $
              CaseE (VarE "z")
              [ ("Leaf",[("num","lnum")], VarE "num")
              , ("Node",[("x","lnodex"),("y","lnodey")],
                 LitE 0)]


locTypeCheckTypecheckerTests :: TestTree
locTypeCheckTypecheckerTests = $(testGroupGenerator)
