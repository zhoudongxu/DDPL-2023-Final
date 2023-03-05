open Syntax
open Support.Error

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec isnumericval t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval t1
  | _ -> false

let rec eval1 t = match t with
    TmIf(_,TmTrue(_),t2,_) ->
      t2
  | TmIf(_,TmFalse(_),_,t3) ->
      t3
  | TmIf(fi,t1,t2,t3) ->
      let t1' = eval1 t1 in
      TmIf(fi, t1', t2, t3)
  | TmSucc(fi,t1) ->
      let t1' = eval1 t1 in
      TmSucc(fi, t1')
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo)
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
      nv1
  | TmPred(fi,t1) ->
      let t1' = eval1 t1 in
      TmPred(fi, t1')
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo)
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
      TmFalse(dummyinfo)
  | TmIsZero(fi,t1) ->
      let t1' = eval1 t1 in
      TmIsZero(fi, t1')
  | _ -> 
      raise NoRuleApplies

let rec eval_big t = match t with 
    TmTrue(_) | TmFalse(_) |TmZero(_) ->
        t
  | TmSucc(fi, t1) -> 
    let t1' = eval_nv t1 in 
    TmSucc(fi, t1')
  | TmPred(fi, t1) -> eval_pred t1
  | TmIsZero(fi, t1) -> eval_iszero(t1)   
  | TmIf(fi,t1,t2,t3) -> eval_if t1 t2 t3

and eval_nv t = match isnumericval(t) with
| true -> t
| false -> let t1 = eval_big(t) in 
match isnumericval(t1) with 
| true -> t1
| false -> raise NoRuleApplies

and eval_pred t =  let t1 = eval_nv(t) in
    match t1 with
    | TmZero(_) -> t1
    | TmSucc(_, nv1) -> nv1
    | _ -> raise NoRuleApplies

and eval_if e1 e2 e3 = match eval_big e1 with
  | TmTrue(_)  -> eval_big e2
  | TmFalse(_) -> eval_big e3
  | _ -> raise NoRuleApplies

and eval_iszero t = match eval_big t with 
| TmZero(_) -> TmTrue(dummyinfo)
| TmSucc(_, nv1) -> TmFalse(dummyinfo)
| _ -> raise NoRuleApplies  

let rec eval t =
  try 
     eval_big t
  with NoRuleApplies -> t


      