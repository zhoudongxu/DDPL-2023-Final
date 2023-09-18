{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

-- |

module Gibbon.MyLocTypeLang.Typecheck
    ( tcExp, tcProg, TCError(..)
    , RegionSet(..)
    , LocationTypeState(..)
    , ConstraintSet(..)
    , LocConstraint(..)
    , Aliased, TcM )
    where

import           Control.DeepSeq
import           Control.Monad.Except
import           Data.Foldable ( foldlM )
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Map as M
import           Data.Maybe
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.MyLocTypeLang.Syntax as L2


 
data LocConstraint = StartOfC LocVar Region 
                   | AfterConstantC Int    
                                    LocVar  
                                    LocVar 
                   | AfterVariableC Var    
                                    LocVar 
                                    LocVar  
                   | InRegionC LocVar Region 
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)



newtype ConstraintSet = ConstraintSet { constraintSet :: S.Set LocConstraint }
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

type Aliased = Bool


newtype LocationTypeState = LocationTypeState
    {
      tsmap :: M.Map LocVar (Modality,Aliased)
    }
    deriving (Read,Show,Eq,Ord, Generic, NFData, Out)

newtype RegionSet = RegionSet { regSet :: S.Set Var }
  deriving (Read, Show, Eq, Ord, Generic, NFData)

type Exp = Exp2

data TCError = GenericTC String Exp
             | VarNotFoundTC Var Exp
             | UnsupportedExpTC Exp
             | LocationTC String Exp LocVar LocVar
             | ModalityTC String Exp LocVar LocationTypeState
               deriving (Read,Eq,Ord,Generic,NFData)

instance Show TCError where
    show (GenericTC str e) = "Error typechecking MyLocTypeLang Program\nIn the expression:\n" ++ (sdoc e) ++ "\n" ++ str ++ "\n"
    show (VarNotFoundTC v e) = "Variable not found: " ++ (show v) ++ "\nIn the expression:\n" ++ (sdoc e) ++ "\n"
    show (UnsupportedExpTC e) = "Unsupported expression:\n" ++ (sdoc e) ++ "\n"
    show (LocationTC str e lv1 lv2) = "Location typechecking error: " ++ str ++ "\nIn the expression:\n" ++ (sdoc e)
                                      ++ "\nLocations: " ++ (show lv1) ++ ", " ++ (show lv2) ++ "\n"
    show (ModalityTC str e lv lts) = "Modality typechecking error: " ++ str ++ "\nIn the expression:\n" ++ (sdoc e)
                                     ++ "\nLocation: " ++ (show lv) ++ "\nLocation type state: " ++ (show lts) ++ "\n"

type TcM a = (Except TCError) a

tcExp :: DDefs Ty2 -> Env2 Ty2 -> FunDefs2
      -> ConstraintSet -> RegionSet -> LocationTypeState -> Exp
      -> TcM (Ty2, LocationTypeState)
tcExp ddfs env funs constrs regs tstatein exp =

    case exp of

      VarE v ->
          do ty <- lookupVar env v exp
             return (ty, tstatein)

      LitE _i -> return (IntTy, tstatein)

      CharE _i -> return (CharTy, tstatein)

      FloatE _i -> return (FloatTy, tstatein)

      LitSymE _v -> return (SymTy, tstatein)

      AppE v ls args ->
          do let (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar) =
                     case M.lookup v funs of
                       Just f -> funTy f
                       Nothing -> error $ "tcExp: Unbound function: " ++ sdoc v
             (in_tys, tstate) <- foldlM
                                   (\(tys, st) a -> do
                                         (ty, st') <- recur st a
                                         pure (tys ++ [ty], st'))
                                   ([],tstatein) args

             if (length args) /= (length in_tys)
               then throwError $ GenericTC ("Arity mismatch. Expected:" ++ show (length in_tys) ++ " Got:" ++ show (length args)) exp
               else pure ()
             mapM (uncurry $ ensureEqualTyNoLoc exp) (fragileZip in_tys arrIns)
             let tyls = concatMap locsInTy in_tys
             case L.find (\loc -> not $ S.member loc (S.fromList ls)) tyls of
               Nothing -> return ()
               Just not_in_ls -> throwError $ GenericTC ("Packed argument location expected: " ++ show not_in_ls) exp
             let handleTS ts (l,Output) =  switchOutLoc exp ts l
                 handleTS ts _ = return ts
             tstate' <- foldM handleTS tstate $ zip ls $ L.map (\(LRM _ _ m) -> m) locVars
             let arrOutMp = M.fromList $ zip (L.map (\(LRM l _ _) -> l) locVars) ls
                 arrOut'  = substLoc arrOutMp arrOut

             return (arrOut',tstate')

      PrimAppE pr es -> do
               let es' = case pr of
                           VSortP{} -> init es
                           InplaceVSortP{} -> init es
                           _        -> es
               (tys,tstate) <- tcExps ddfs env funs constrs regs tstatein es'

               let len2 = checkLen exp pr 2 es
                   len1 = checkLen exp pr 1 es
                   len0 = checkLen exp pr 0 es
                   len3 = checkLen exp pr 3 es
                   len4 = checkLen exp pr 4 es

                   mk_bools = do
                     len0
                     pure (BoolTy, tstate)

                   bool_ops = do
                     len2
                     _ <- ensureEqualTy (es !! 0) BoolTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) BoolTy (tys !! 1)
                     pure (BoolTy, tstate)

                   int_ops = do
                     len2
                     _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
                     pure (IntTy, tstate)

                   float_ops = do
                     len2
                     _ <- ensureEqualTy (es !! 0) FloatTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) FloatTy (tys !! 1)
                     pure (FloatTy, tstate)

                   int_cmps = do
                     len2
                     _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
                     pure (BoolTy, tstate)

                   float_cmps = do
                     len2
                     _ <- ensureEqualTy (es !! 0) FloatTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) FloatTy (tys !! 1)
                     pure (BoolTy, tstate)
                   
                   char_cmps = do 
                     len2
                     _ <- ensureEqualTy (es !! 0) CharTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) CharTy (tys !! 1)
                     pure (BoolTy, tstate)

               case pr of
                 MkTrue  -> mk_bools
                 MkFalse -> mk_bools
                 AddP    -> int_ops
                 SubP    -> int_ops
                 MulP    -> int_ops
                 DivP    -> int_ops
                 ModP    -> int_ops
                 ExpP    -> int_ops
                 FAddP   -> float_ops
                 FSubP   -> float_ops
                 FMulP   -> float_ops
                 FDivP   -> float_ops
                 FExpP   -> float_ops
                 EqIntP  -> int_cmps
                 LtP     -> int_cmps
                 GtP     -> int_cmps
                 LtEqP   -> int_cmps
                 GtEqP   -> int_cmps
                 EqFloatP -> float_cmps
                 EqCharP  -> char_cmps
                 FLtP     -> float_cmps
                 FGtP     -> float_cmps
                 FLtEqP   -> float_cmps
                 FGtEqP   -> float_cmps
                 OrP     -> bool_ops
                 AndP    -> bool_ops

                 RandP -> return (IntTy, tstate)
                 FRandP -> return (FloatTy, tstate)

                 FloatToIntP -> do
                   len1
                   ensureEqualTy exp FloatTy (tys !! 0)
                   return (IntTy, tstate)

                 IntToFloatP -> do
                   len1
                   ensureEqualTy exp IntTy (tys !! 0)
                   return (FloatTy, tstate)

                 FSqrtP -> do
                   len1
                   ensureEqualTy exp FloatTy (tys !! 0)
                   return (FloatTy, tstate)

                 FTanP -> do
                   len1
                   ensureEqualTy exp FloatTy (tys !! 0)
                   return (FloatTy, tstate)

                 Gensym -> len0 >>= \_ -> pure (SymTy, tstate)

                 EqSymP -> do
                   len2
                   ensureEqualTy exp SymTy (tys !! 0)
                   ensureEqualTy exp SymTy (tys !! 1)
                   return (BoolTy,tstate)

                 EqBenchProgP _ -> do
                   len0
                   return (BoolTy,tstate)

                 DictEmptyP ty -> do
                   len1
                   let [a] = tys
                   _ <- ensureEqualTy exp ArenaTy a
                   case es !! 0 of
                     (VarE var) ->
                         do ensureArenaScope exp env (Just var)
                            return (SymDictTy (Just var) (stripTyLocs ty), tstate)
                     _ -> throwError $ GenericTC "Expected arena variable argument" exp

                 DictInsertP ty -> do
                   len4
                   let [a,d,k,v]  = tys
                   _ <- ensureEqualTy exp ArenaTy a
                   _ <- ensureEqualTy exp SymTy k
                   _ <- ensureEqualTyNoLoc exp ty v
                   case d of
                     SymDictTy ar _ty ->
                         case es !! 0 of
                           (VarE var) ->
                               do ensureArenaScope exp env ar
                                  ensureArenaScope exp env (Just var)
                                  return (SymDictTy (Just var) (stripTyLocs ty), tstate)
                           _ -> throwError $ GenericTC "Expected arena variable argument" exp
                     _ -> throwError $ GenericTC "Expected SymDictTy" exp

                 DictLookupP ty -> do
                   len2
                   let [d,k]  = tys
                   case d of
                     SymDictTy ar _ty ->
                         do _ <- ensureEqualTy exp SymTy k
                            ensureArenaScope exp env ar
                            return (ty, tstate)
                     _ -> throwError $ GenericTC "Expected SymDictTy" exp

                 DictHasKeyP _ty -> do
                   len2
                   let [d,k]  = tys
                   case d of
                     SymDictTy ar _ty -> do _ <- ensureEqualTy exp SymTy k
                                            ensureArenaScope exp env ar
                                            return (BoolTy, tstate)
                     _ -> throwError $ GenericTC "Expected SymDictTy" exp

                 SizeParam -> do
                   len0
                   return (IntTy, tstate)

                 IsBig -> do
                   len2
                   let [ity, ety] = tys
                   ensureEqualTy exp ity IntTy
                   if isPackedTy ety
                   then pure (BoolTy, tstate)
                   else error "L1.Typecheck: IsBig expects a Packed value."

                 ErrorP _str ty -> do
                   len0
                   return (ty, tstate)

                 ReadPackedFile _fp _tycon _reg ty -> do
                   len0
                   return (ty, tstate)

                 WritePackedFile _ ty
                   | PackedTy{} <- ty  -> do
                     len1
                     let [packed_ty] = tys
                     _ <- ensureEqualTy exp packed_ty ty
                     pure (ProdTy [], tstate)
                   | otherwise -> error $ "writePackedFile expects a packed type. Given" ++ sdoc ty

                 ReadArrayFile _ ty -> do
                   len0
                   if isValidListElemTy ty
                   then return (VectorTy ty, tstate)
                   else throwError $ GenericTC "Not a valid list type" exp

                 RequestEndOf -> do
                   len1
                   case (es !! 0) of
                     VarE{} -> if isPackedTy (tys !! 0)
                               then return (CursorTy, tstate)
                               else case (tys !! 0) of
                                      SymTy -> return (CursorTy, tstate)
                                      IntTy -> return (CursorTy, tstate)
                                      CursorTy -> return (CursorTy, tstate)
                                      ty -> throwError $ GenericTC ("Expected PackedTy, got " ++ sdoc ty)  exp
                     _ -> throwError $ GenericTC "Expected a variable argument" exp

                 RequestSizeOf -> do
                   len1
                   case (es !! 0) of
                     VarE{} -> if isPackedTy (tys !! 0)
                               then return (IntTy, tstate)
                               else case (tys !! 0) of
                                      SymTy -> return (IntTy, tstate)
                                      IntTy -> return (IntTy, tstate)
                                      _ -> throwError $ GenericTC "Expected PackedTy" exp
                     _ -> throwError $ GenericTC "Expected a variable argument" exp

                 VAllocP elty -> do
                   len1
                   checkListElemTy elty
                   let [i] = tys
                   _ <- ensureEqualTy (es !! 0) IntTy i
                   pure (VectorTy elty, tstate)

                 VFreeP elty -> do
                   len1
                   checkListElemTy elty
                   let [i] = tys
                   _ <- ensureEqualTy (es !! 0) (VectorTy elty) i
                   pure (ProdTy [], tstate)

                 VFree2P elty -> do
                   len1
                   checkListElemTy elty
                   let [i] = tys
                   _ <- ensureEqualTy (es !! 0) (VectorTy elty) i
                   pure (ProdTy [], tstate)

                 VLengthP elty -> do
                   let [ls] = tys
                   _ <- ensureEqualTy exp (VectorTy elty) ls
                   pure (IntTy, tstate)

                 VNthP elty -> do
                   let [ls, i] = tys
                   _ <- ensureEqualTy exp (VectorTy elty) ls
                   _ <- ensureEqualTy exp IntTy i
                   pure (elty, tstate)

                 VSliceP elty   -> do
                   let [from,to,ls] = tys
                   _ <- ensureEqualTy exp IntTy from
                   _ <- ensureEqualTy exp IntTy to
                   _ <- ensureEqualTy exp (VectorTy elty) ls
                   pure (VectorTy elty, tstate)

                 InplaceVUpdateP elty -> do
                   let [ls,i,val] = tys
                   _ <- ensureEqualTy exp (VectorTy elty) ls
                   _ <- ensureEqualTy exp IntTy i
                   _ <- ensureEqualTy exp elty val
                   pure (VectorTy elty, tstate)

                 VConcatP elty -> do
                   len1
                   let [ls] = tys
                   _ <- ensureEqualTy (es !! 0) (VectorTy (VectorTy elty)) ls
                   pure (VectorTy elty, tstate)

                 VSortP elty ->
                   case (es !! 1) of
                     VarE f -> do
                       len2
                       let [ls]   = tys
                           fn_ty  = lookupFEnv f env
                           in_tys = inTys fn_ty
                           ret_ty = outTy fn_ty
                           err x  = throwError $ GenericTC ("vsort: Expected a sort function of type (ty -> ty -> Bool). Got"++ sdoc x) exp
                       _ <- ensureEqualTy (es !! 0) (VectorTy elty) ls
                       case in_tys of
                         [a,b] -> do
                            _ <- ensureEqualTy (es !! 1) a elty
                            _ <- ensureEqualTy (es !! 1) b elty
                            _ <- ensureEqualTy (es !! 1) ret_ty IntTy
                            pure (VectorTy elty, tstate)
                         _ -> err fn_ty
                     oth -> throwError $ GenericTC ("vsort: function pointer has to be a variable reference. Got"++ sdoc oth) exp

                 InplaceVSortP elty -> recur tstatein (PrimAppE (VSortP elty) es)

                 VMergeP elty -> do
                   len2
                   checkListElemTy elty
                   let [ls1,ls2] = tys
                   _ <- ensureEqualTy (es !! 0) (VectorTy elty) ls1
                   _ <- ensureEqualTy (es !! 1) (VectorTy elty) ls2
                   pure (VectorTy elty, tstate)

                 PDictInsertP kty vty -> do
                   len3
                   checkListElemTy kty
                   checkListElemTy vty
                   let [key, val, dict] = tys
                   _ <- ensureEqualTy (es !! 0) key kty
                   _ <- ensureEqualTy (es !! 1) val vty
                   _ <- ensureEqualTy (es !! 2) dict (PDictTy kty vty)
                   pure (PDictTy kty vty, tstate)

                 PDictLookupP kty vty -> do
                   len2
                   checkListElemTy kty
                   checkListElemTy vty
                   let [key, dict] = tys
                   _ <- ensureEqualTy (es !! 0) key kty
                   _ <- ensureEqualTy (es !! 1) dict (PDictTy kty vty)
                   pure (vty, tstate)

                 PDictAllocP kty vty -> do
                   len0
                   checkListElemTy kty
                   checkListElemTy vty
                   pure (PDictTy kty vty, tstate)

                 PDictHasKeyP kty vty -> do
                   len2
                   checkListElemTy kty
                   checkListElemTy vty
                   let [key, dict] = tys
                   _ <- ensureEqualTy (es !! 0) key kty
                   _ <- ensureEqualTy (es !! 1) dict (PDictTy kty vty)
                   pure (BoolTy, tstate)

                 PDictForkP kty vty -> do
                   len1
                   checkListElemTy kty
                   checkListElemTy vty
                   let [dict] = tys
                   _ <- ensureEqualTy (es !! 0) dict (PDictTy kty vty)
                   pure (ProdTy [PDictTy kty vty, PDictTy kty vty], tstate)

                 PDictJoinP kty vty -> do
                   len2
                   checkListElemTy kty
                   checkListElemTy vty
                   let [dict1, dict2] = tys
                   _ <- ensureEqualTy (es !! 0) dict1 (PDictTy kty vty)
                   _ <- ensureEqualTy (es !! 1) dict2 (PDictTy kty vty)
                   pure (PDictTy kty vty, tstate)

                 LLAllocP elty -> do
                   len0
                   checkListElemTy elty
                   pure (ListTy elty, tstate)

                 LLIsEmptyP elty -> do
                   len1
                   checkListElemTy elty
                   let [ll] = tys
                   _ <- ensureEqualTy (es !! 0) ll (ListTy elty)
                   pure (BoolTy, tstate)

                 LLConsP elty -> do
                   len2
                   checkListElemTy elty
                   let [elt, ll] = tys
                   _ <- ensureEqualTy (es !! 0) elt elty
                   _ <- ensureEqualTy (es !! 1) ll (ListTy elty)
                   pure (ListTy elty, tstate)

                 LLHeadP elty -> do
                   len1
                   checkListElemTy elty
                   let [ll] = tys
                   _ <- ensureEqualTy (es !! 0) ll (ListTy elty)
                   pure (elty, tstate)

                 LLTailP elty -> do
                   len1
                   checkListElemTy elty
                   let [ll] = tys
                   _ <- ensureEqualTy (es !! 0) ll (ListTy elty)
                   pure (ListTy elty, tstate)

                 LLFreeP elty -> do
                   len1
                   checkListElemTy elty
                   let [i] = tys
                   _ <- ensureEqualTy (es !! 0) (ListTy elty) i
                   pure (ProdTy [], tstate)

                 LLFree2P elty -> do
                   len1
                   checkListElemTy elty
                   let [i] = tys
                   _ <- ensureEqualTy (es !! 0) (ListTy elty) i
                   pure (ProdTy [], tstate)

                 LLCopyP elty -> do
                   len1
                   checkListElemTy elty
                   let [i] = tys
                   _ <- ensureEqualTy (es !! 0) (ListTy elty) i
                   pure (ListTy elty, tstate)

                 GetNumProcessors -> do
                   len0
                   pure (IntTy, tstate)

                 PrintInt -> do
                   len1
                   _ <- ensureEqualTy (es !!! 0) IntTy (tys !!! 0)
                   pure (ProdTy [], tstate)

                 PrintChar -> do
                   len1
                   _ <- ensureEqualTy (es !!! 0) CharTy (tys !!! 0)
                   pure (ProdTy [], tstate)

                 PrintFloat -> do
                   len1
                   _ <- ensureEqualTy (es !!! 0) FloatTy (tys !!! 0)
                   pure (ProdTy [], tstate)

                 PrintBool -> do
                   len1
                   _ <- ensureEqualTy (es !!! 0) BoolTy (tys !!! 0)
                   pure (ProdTy [], tstate)

                 PrintSym -> do
                   len1
                   _ <- ensureEqualTy (es !!! 0) SymTy (tys !!! 0)
                   pure (ProdTy [], tstate)

                 ReadInt  -> throwError $ GenericTC "ReadInt not handled" exp

                 SymSetEmpty -> do
                   len0
                   pure (SymSetTy, tstate)

                 SymSetInsert -> do
                   len2
                   _ <- ensureEqualTy (es !!! 0) SymSetTy (tys !!! 0)
                   _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
                   pure (SymSetTy, tstate)

                 SymSetContains -> do
                   len2
                   _ <- ensureEqualTy (es !!! 0) SymSetTy (tys !!! 0)
                   _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
                   pure (BoolTy, tstate)

                 SymHashEmpty -> do
                   len0
                   pure (SymHashTy, tstate)

                 SymHashInsert -> do
                   len3
                   _ <- ensureEqualTy (es !!! 0) SymHashTy (tys !!! 0)
                   _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
                   _ <- ensureEqualTy (es !!! 2) SymTy (tys !!! 2)
                   pure (SymHashTy, tstate)

                 SymHashLookup -> do
                   len2
                   _ <- ensureEqualTy (es !!! 0) SymHashTy (tys !!! 0)
                   _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
                   pure (SymTy, tstate)

                 SymHashContains -> do
                   len2
                   _ <- ensureEqualTy (es !!! 0) SymHashTy (tys !!! 0)
                   _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
                   pure (BoolTy, tstate)

                 IntHashEmpty -> do
                   len0
                   pure (IntHashTy, tstate)

                 IntHashInsert -> do
                   len3
                   _ <- ensureEqualTy (es !!! 0) IntHashTy (tys !!! 0)
                   _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
                   _ <- ensureEqualTy (es !!! 2) IntTy (tys !!! 2)
                   pure (IntHashTy, tstate)

                 IntHashLookup -> do
                   len2
                   _ <- ensureEqualTy (es !!! 0) IntHashTy (tys !!! 0)
                   _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
                   pure (IntTy, tstate)

                 Write3dPpmFile{} -> throwError $ GenericTC "Write3dPpmFile not handled yet" exp


      LetE (v,_ls,ty,e1) e2 -> do

               (ty1,tstate1) <- recur tstatein e1
               ensureEqualTyNoLoc exp ty1 ty
               let env' = extendVEnv v ty env

               tcExp ddfs env' funs constrs regs tstate1 e2

      IfE e1 e2 e3 -> do

               (ty1,tstate1) <- recur tstatein e1
               ensureEqualTyModCursor exp ty1 BoolTy

               (ty2,tstate2) <- recur tstate1 e2
               (ty3,tstate3) <- recur tstate1 e3

               tstate <- combineTStates exp tstate2 tstate3

               ensureEqualTyModCursor exp ty2 ty3
               return (ty2,tstate)

      MkProdE es -> do
               (tys,tstate) <- tcExps ddfs env funs constrs regs tstatein es
               return (ProdTy tys,tstate)

      ProjE i e -> do

               (ty,tstate) <- recur tstatein e
               tyi <- tcProj exp i ty
               return (tyi, tstate)

      CaseE e brs -> do

               (ty,tstate) <- recur tstatein e
               case ty of
                 PackedTy _dc lin -> do
                         reg <- getRegion e constrs lin
                         ensureMatchCases ddfs exp ty brs
                         (tys,tstate') <- tcCases ddfs env funs constrs regs tstate lin reg brs
                         foldM_ (ensureEqualTyModCursor exp) (tys !! 0) (tail tys)
                         return (tys !! 0,tstate')
                 _ -> error ("Expected packed type, got " ++ show ty)

      DataConE l dc es -> do
               let dcty = getTyOfDataCon ddfs dc
               (tys,tstate1) <- tcExps ddfs env funs constrs regs tstatein es
               let args = lookupDataCon ddfs dc

               if length args /= length es
               then throwError $ GenericTC "Invalid argument length" exp
               else do
                 sequence_ [ ensureEqualTyNoLoc exp ty1 ty2
                           | (ty1,ty2) <- zip args tys ]
                 ensureDataCon exp l tys constrs
                 tstate2 <- switchOutLoc exp tstate1 l
                 return (PackedTy dcty l, tstate2)

      TimeIt e _ty _b -> do

               (ty1,tstate1) <- recur tstatein e
               return (ty1,tstate1)

      SpawnE f locs args ->
        tcExp ddfs env funs constrs regs tstatein (AppE f locs args)

      SyncE -> pure (ProdTy [], tstatein)

      WithArenaE v e -> do
              let env' = extendVEnv v ArenaTy env
              tcExp ddfs env' funs constrs regs tstatein e

      MapE _ _ -> throwError $ UnsupportedExpTC exp

      FoldE _ _ _ -> throwError $ UnsupportedExpTC exp

      Ext (LetRegionE r _ _ e) -> do
               regs' <- regionInsert exp r regs
               (ty,tstate) <- tcExp ddfs env funs constrs regs' tstatein e
               return (ty,tstate)

      Ext (LetParRegionE r _ _ e) -> do
               regs' <- regionInsert exp r regs
               (ty,tstate) <- tcExp ddfs env funs constrs regs' tstatein e
               return (ty,tstate)

      Ext (LetLocE v c e) -> do
              let env' = extendVEnv v CursorTy env
              case c of
                StartOfLE r ->
                    do ensureRegion exp r regs
                       absentStart exp constrs r
                       let tstate1 = extendTS v (Output,False) tstatein
                       let constrs1 = extendConstrs (StartOfC v r) $ extendConstrs (InRegionC v r) constrs
                       (ty,tstate2) <- tcExp ddfs env' funs constrs1 regs tstate1 e
                       tstate3 <- removeLoc exp tstate2 v
                       return (ty,tstate3)
                AfterConstantLE i l1 ->
                     do r <- getRegion exp constrs l1
                        let tstate1 = extendTS v (Output,True) $ setAfter l1 tstatein
                        let constrs1 = extendConstrs (InRegionC v r) $ extendConstrs (AfterConstantC i l1 v) constrs
                        (ty,tstate2) <- tcExp ddfs env' funs constrs1 regs tstate1 e
                        tstate3 <- removeLoc exp tstate2 v
                        return (ty,tstate3)
                AfterVariableLE x l1 _ ->
                    do r <- getRegion exp constrs l1
                       (_xty,tstate1) <- tcExp ddfs env funs constrs regs tstatein $ VarE x
                       let tstate2 = extendTS v (Output,True) $ setAfter l1 tstate1
                       let constrs1 = extendConstrs (InRegionC v r) $ extendConstrs (AfterVariableC x l1 v) constrs
                       (ty,tstate3) <- tcExp ddfs env' funs constrs1 regs tstate2 e
                       tstate4 <- removeLoc exp tstate3 v
                       return (ty,tstate4)
                FromEndLE _l1 ->
                    do
                      (ty,tstate1) <- tcExp ddfs env' funs constrs regs tstatein e
                      return (ty,tstate1)
                FreeLE ->
                    do let constrs1 = extendConstrs (InRegionC v globalReg) $ constrs
                       (ty,tstate1) <- tcExp ddfs env' funs constrs1 regs tstatein e
                       return (ty,tstate1)
                _ -> throwError $ GenericTC "Invalid letloc form" exp

      Ext (FromEndE{}) -> throwError $ GenericTC "FromEndE not handled" exp
      Ext (AddFixed{}) -> return (CursorTy,tstatein)

      Ext (RetE _ls v) -> do
               recur tstatein $ VarE v

      Ext (BoundsCheck{}) -> return (IntTy,tstatein)

      Ext (IndirectionE tycon _ (a,_) _ _) -> return (PackedTy tycon a, tstatein)

      Ext GetCilkWorkerNum -> return (IntTy, tstatein)

      Ext (LetAvail _ e) -> recur tstatein e

    where recur ts e = tcExp ddfs env funs constrs regs ts e
          checkListElemTy el_ty =
            if isValidListElemTy el_ty
            then pure ()
            else throwError $ GenericTC ("Gibbon-TODO: Lists of only scalars or flat products of scalars are allowed. Got" ++ sdoc el_ty) exp


tcCases :: DDefs Ty2 -> Env2 Ty2 -> FunDefs2
        -> ConstraintSet -> RegionSet -> LocationTypeState -> LocVar
        -> Region -> [(DataCon, [(Var,LocVar)], Exp)]
        -> TcM ([Ty2], LocationTypeState)
tcCases ddfs env funs constrs regs tstatein lin reg ((dc, vs, e):cases) = do

  let argtys = zip vs $ lookupDataCon ddfs dc
      pairwise = zip argtys $ Nothing : (L.map Just argtys)

      genConstrs (((_v1,l1),PackedTy _ _),Nothing) (lin,lst) =
          (l1,[AfterConstantC 1 lin l1, InRegionC l1 reg] ++ lst)
      genConstrs (((_v1,l1),PackedTy _ _),Just ((v2,l2),PackedTy _ _)) (_lin,lst) =
          (l1,[AfterVariableC v2 l2 l1, InRegionC l1 reg] ++ lst)
      genConstrs (((_v1,l1),PackedTy _ _),Just ((_v2,_l2),IntTy)) (lin,lst) =
        let sz = fromMaybe 1 (sizeOfTy IntTy)
        in (l1, [AfterConstantC sz lin l1, InRegionC l1 reg] ++ lst)
      genConstrs (((_,l1),_),_) (lin,lst) =
        (lin, (InRegionC l1 reg : lst))

      genTS ((_v,l),PackedTy _ _) ts = extendTS l (Input,False) ts
      genTS _ ts = ts
      genEnv ((v,l),PackedTy dc _l') env = extendVEnv v (PackedTy dc l) env
      genEnv ((v,_l),ty) env = extendVEnv v ty env

      remTS ((_v,l),PackedTy _ _) ts = removeTS l ts
      remTS _ ts = ts

      constrs1 = L.foldr extendConstrs constrs $ snd $ L.foldr genConstrs (lin,[]) pairwise
      tstate1 = L.foldr genTS tstatein argtys
      env1 = L.foldr genEnv env argtys

  (ty1,tstate2) <- tcExp ddfs env1 funs constrs1 regs tstate1 e
  (tyRest,tstateRest) <- recur
  tstateCombine <- combineTStates e tstate2 tstateRest
  let tstatee' = L.foldr remTS tstateCombine argtys
  return (ty1:tyRest,tstatee')

    where recur = do
            (tys,tstate2) <- tcCases ddfs env funs constrs regs tstatein lin reg cases
            return (tys,tstate2)

tcCases _ _ _ _ _ ts _ _ [] = return ([],ts)

tcProj :: Exp -> Int -> Ty2 -> TcM Ty2
tcProj _ i (ProdTy tys) = return $ tys !! i
tcProj e _i ty = throwError $ GenericTC ("Projection from non-tuple type " ++ (show ty)) e


tcExps :: DDefs Ty2 -> Env2 Ty2 -> FunDefs2
      -> ConstraintSet -> RegionSet -> LocationTypeState -> [Exp]
      -> TcM ([Ty2], LocationTypeState)
tcExps ddfs env funs constrs regs tstatein (exp:exps) =
    do (ty,ts) <- tcExp ddfs env funs constrs regs tstatein exp
       (tys,ts') <- tcExps ddfs env funs constrs regs ts exps
       return (ty:tys,ts')
tcExps _ _ _ _ _ ts [] = return ([],ts)



tcProg :: Prog2 -> PassM Prog2
tcProg prg0@Prog{ddefs,fundefs,mainExp} = do

  -- Handle functions
  mapM_ fd $ M.elems fundefs

  -- Handle main function
  case mainExp of
    Nothing -> return ()
    Just (e,t) ->
        let init_env = progToEnv prg0
            res = runExcept $ tcExp ddefs init_env fundefs
                    (ConstraintSet $ S.empty) (RegionSet $ S.empty)
                    (LocationTypeState $ M.empty) e
        in case res of
             Left err -> error $ show err
             Right (t',_ts) ->
                 if t' == t then return ()
                 else error $ "Expected type " ++ (show t) ++ " and got type " ++ (show t')

  return prg0 -- Identity function for now.

  where

    fd :: FunDef2 -> PassM ()
    fd func@FunDef{funTy,funArgs,funBody} = do
        let init_env = progToEnv prg0
            env = extendsVEnv (M.fromList $ zip funArgs (arrIns funTy)) init_env
            constrs = funConstrs (locVars funTy)
            regs = funRegs (locVars funTy)
            tstate = funTState (locVars funTy)
            res = runExcept $ tcExp ddefs env fundefs constrs regs tstate funBody
        case res of
          Left err -> error $ show err
          Right (ty,_) -> if ty == (arrOut funTy)
                          then return ()
                          else error $ "Expected type " ++ (sdoc (arrOut funTy))
                                    ++ " and got type " ++ (sdoc ty)
                                    ++ " in\n" ++ (sdoc func)


regionInsert :: Exp -> Region -> RegionSet -> TcM RegionSet
regionInsert e r (RegionSet regSet) = do
  if (S.member (regionToVar r) regSet)
  then throwError $ GenericTC "Shadowed regions not allowed" e
  else return $ RegionSet (S.insert (regionToVar r) regSet)


hasRegion :: Region -> RegionSet -> Bool
hasRegion r (RegionSet regSet) = S.member (regionToVar r) regSet


ensureRegion :: Exp -> Region -> RegionSet -> TcM ()
ensureRegion exp r (RegionSet regSet) =
    if S.member (regionToVar r) regSet then return ()
    else throwError $ GenericTC ("Region " ++ (show r) ++ " not in scope") exp

getRegion :: Exp -> ConstraintSet -> LocVar -> TcM Region
getRegion exp (ConstraintSet cs) l = go $ S.toList cs
    where go ((InRegionC l1 r):cs) = if l1 == l then return r
                                     else go cs
          go (_:cs) = go cs
          go [] = throwError $ GenericTC ("Location " ++ (show l) ++ " has no region") exp


funRegs :: [LRM] -> RegionSet
funRegs ((LRM _l r _m):lrms) =
    let (RegionSet rs) = funRegs lrms
    in RegionSet $ S.insert (regionToVar r) rs
funRegs [] = RegionSet $ S.empty

globalReg :: Region
globalReg = GlobR "GLOBAL" BigInfinite

funConstrs :: [LRM] -> ConstraintSet
funConstrs ((LRM l r _m):lrms) =
    extendConstrs (InRegionC l r) $ funConstrs lrms
funConstrs [] = ConstraintSet $ S.empty

funTState :: [LRM] -> LocationTypeState
funTState ((LRM l _r m):lrms) =
    extendTS l (m,False) $ funTState lrms
funTState [] = LocationTypeState $ M.empty

lookupVar :: Env2 Ty2 -> Var -> Exp -> TcM Ty2
lookupVar env var exp =
    case M.lookup var $ vEnv env of
      Nothing -> throwError $ VarNotFoundTC var exp
      Just ty -> return ty


combineTStates :: Exp -> LocationTypeState -> LocationTypeState -> TcM LocationTypeState
combineTStates _exp (LocationTypeState ts1) (LocationTypeState ts2) =
    return $ LocationTypeState $ M.union ts1 ts2

ensureEqual :: Eq a => Exp -> String -> a -> a -> TcM a
ensureEqual exp str a b = if a == b then return a else throwError $ GenericTC str exp

-- | Ensure that the number of arguments to an operation is correct.
checkLen :: (Show op, Show arg) => Exp -> op -> Int -> [arg] -> TcM ()
checkLen expr pr n ls =
  if length ls == n
  then return ()
  else throwError $ GenericTC ("Wrong number of arguments to "++show pr++
                               ".\nExpected "++show n++", received "
                                ++show (length ls)++":\n  "++show ls) expr

ensureEqualTy :: Exp -> Ty2 -> Ty2 -> TcM Ty2
ensureEqualTy _ CursorTy IntTy = return CursorTy
ensureEqualTy _ IntTy CursorTy = return CursorTy
ensureEqualTy exp a b = ensureEqual exp ("Expected these types to be the same: "
                                         ++ (show a) ++ ", " ++ (show b)) a b

ensureEqualTyModCursor :: Exp -> Ty2 -> Ty2 -> TcM Ty2
ensureEqualTyModCursor _exp CursorTy (PackedTy _ _) = return CursorTy
ensureEqualTyModCursor _exp (PackedTy _ _) CursorTy = return CursorTy
ensureEqualTyModCursor exp a b = ensureEqualTy exp a b

ensureEqualTyNoLoc :: Exp -> Ty2 -> Ty2 -> TcM Ty2
ensureEqualTyNoLoc exp ty1 ty2 =
  case (ty1,ty2) of
    (SymDictTy _ar1 ty1, SymDictTy _ar2 ty2) ->
        do ty1' <- dummyTyLocs ty1
           ty2' <- dummyTyLocs ty2
           ensureEqualTyNoLoc exp ty1' ty2'
    (PackedTy dc1 _, PackedTy dc2 _) -> if dc1 == dc2
                                        then return ty1
                                        else ensureEqualTy exp ty1 ty2
    (ProdTy tys1, ProdTy tys2) -> do
        checks <- return $ L.map (\(ty1,ty2) -> ensureEqualTyNoLoc exp ty1 ty2) (zip tys1 tys2)
        -- TODO: avoid runExcept here
        forM_ checks $ \c -> do
            let c' = runExcept c
            case c' of
              Left err -> throwError err
              Right _  -> return ()
        return ty1
    _ -> ensureEqualTyModCursor exp ty1 ty2

ensureMatchCases :: DDefs Ty2 -> Exp -> Ty2 -> [(DataCon, [(Var,LocVar)], Exp)] -> TcM ()
ensureMatchCases ddfs exp ty cs = do
  case ty of
    PackedTy tc _l -> do
            let cons = S.fromList $ L.map fst $ dataCons $ lookupDDef ddfs tc
            forM cs $ \(dc,_,_) ->
                do if S.member dc cons
                   then return ()
                   else throwError $ GenericTC "Invalid case statement" exp
            return ()
    _ -> throwError $ GenericTC "Cannot case on non-packed type" exp


ensurePackedLoc :: Exp -> Ty2 -> LocVar -> TcM ()
ensurePackedLoc exp ty l =
    case ty of
      PackedTy _ l1 -> if l1 == l then return ()
                       else throwError $ GenericTC ("Wrong location in type " ++ (show ty)) exp
      _ -> throwError $ GenericTC "Expected a packed type" exp

ensureDataCon :: Exp -> LocVar -> [Ty2] -> ConstraintSet -> TcM ()
ensureDataCon exp linit0 tys cs = (go Nothing linit0 tys)
    where go Nothing linit ((PackedTy dc l):tys) = do
            ensureAfterConstant exp cs linit l
            go (Just (PackedTy dc l)) l tys

          go Nothing linit (_ty:tys) = do
            case getAfterConstant cs linit of
              Nothing     -> go Nothing linit tys
              Just linit' -> go Nothing linit' tys

          go (Just (PackedTy _dc1 l1)) _linit ((PackedTy dc2 l2):tys) = do
            ensureAfterPacked exp cs l1 l2
            go (Just (PackedTy dc2 l2)) l2 tys

          go (Just (PackedTy _dc _l1)) linit (_ty:tys) =
              go Nothing linit tys
          go _ _ [] = return ()
          go _ _ _  = internalError "Unxpected case reached: MyLocTypeLang :ensureDataCon"



ensureAfterConstant :: Exp -> ConstraintSet -> LocVar -> LocVar -> TcM ()
ensureAfterConstant exp (ConstraintSet cs) l1 l2 =
    if L.any f $ S.toList cs then return ()
    else throwError $ LocationTC "Expected after constant relationship" exp l1 l2
    -- l1 is before l2
    where f (AfterConstantC _i l1' l2') = l1' == l1 && l2' == l2
          f _ = False


ensureAfterPacked :: Exp -> ConstraintSet -> LocVar -> LocVar -> TcM ()
ensureAfterPacked  exp (ConstraintSet cs) l1 l2 =
    if L.any f $ S.toList cs then return ()
    else throwError $ LocationTC "Expected after packed relationship" exp l1 l2
    where f (AfterVariableC _v l1' l2') = l1' == l1 && l2' == l2
          f _ = False

getAfterConstant :: ConstraintSet -> LocVar -> Maybe LocVar
getAfterConstant (ConstraintSet cs) l0 =
  let mb_cs = L.find (\c -> case c of
                         AfterConstantC _i l1 _l2 | l1 == l0 -> True
                         _ -> False)
              cs
  in case mb_cs of
       Just (AfterConstantC _i _l1 l2) -> Just l2
       _ -> Nothing


extendTS
  :: LocVar
     -> (Modality, Aliased) -> LocationTypeState -> LocationTypeState
extendTS v d (LocationTypeState ls) = LocationTypeState $ M.insert v d ls

removeTS :: LocVar -> LocationTypeState -> LocationTypeState
removeTS l (LocationTypeState ls) = LocationTypeState $ M.delete l ls

setAfter :: LocVar -> LocationTypeState -> LocationTypeState
setAfter l (LocationTypeState ls) = LocationTypeState $ M.adjust (\(m,_) -> (m,True)) l ls

_lookupTS :: Exp -> LocVar -> LocationTypeState -> TcM (Modality,Bool)
_lookupTS exp l (LocationTypeState ls) =
    case M.lookup l ls of
      Nothing -> throwError $ GenericTC ("Failed lookup of location " ++ (show l)) exp
      Just d -> return d

extendConstrs :: LocConstraint -> ConstraintSet -> ConstraintSet
extendConstrs c (ConstraintSet cs) = ConstraintSet $ S.insert c cs

switchOutLoc :: Exp -> LocationTypeState -> LocVar -> TcM LocationTypeState
switchOutLoc exp ts@(LocationTypeState ls) l =
    case M.lookup l ls of
      Nothing -> throwError $ GenericTC ("Unknown location " ++ (show l)) exp
      Just (Output,a) -> return $ LocationTypeState $ M.update (\_ -> Just (Input,a)) l ls
      Just (Input,_a) -> return ts

_absentAfter :: Exp -> LocationTypeState -> LocVar -> TcM ()
_absentAfter exp (LocationTypeState ls) l =
    case M.lookup l ls of
      Nothing -> throwError $ GenericTC ("Unknown location " ++ (show l)) exp
      Just (_m,False) -> return ()
      Just (_m,True) -> throwError $ GenericTC ("Alias of location " ++ (show l)) exp

absentStart :: Exp -> ConstraintSet -> Region -> TcM ()
absentStart exp (ConstraintSet cs) r = go $ S.toList cs
    where go ((StartOfC _l r'):cs) =
              if r == r'
              then throwError $ GenericTC ("Repeated start of " ++ (show r)) exp
              else go cs
          go (_:cs) = go cs
          go [] = return ()


removeLoc :: Exp -> LocationTypeState -> LocVar -> TcM LocationTypeState
removeLoc exp (LocationTypeState ls) l =
    if M.member l ls
    then return $ LocationTypeState $ M.delete l ls
    else throwError $ GenericTC ("Cannot remove location " ++ (show l)) exp

ensureArenaScope :: MonadError TCError m => Exp -> Env2 a -> Maybe Var -> m ()
ensureArenaScope exp env ar =
    case ar of
      Nothing -> throwError $ GenericTC "Expected arena annotation" exp
      Just var -> unless (S.member var . M.keysSet . vEnv $ env) $
                  throwError $ GenericTC ("Expected arena in scope: " ++ sdoc var) exp
