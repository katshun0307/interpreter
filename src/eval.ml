(** Define normal reduction *)

open Syntax
module E = Environment.Environment
open Core
open Classifier_modules
open Option

let ( = ) = Stdlib.( = )

exception EvalError of string
exception Error of string
exception NotValue

let string_of_env = E.to_string ~f:string_of_tm

(** Return unit if the given term is a value at [~stage]. Raise error [NotValue] otherwise. *)
let rec is_value_exn ~stage = function
  | v when Stage.is_empty stage ->
    (match v with
    (* when stage is empty *)
    | TmLam (_, _, _) -> ()
    | Quote (a, t) -> is_value_exn ~stage:(Stage.add_classifier a stage) t
    | Gen (_, t) -> is_value_exn ~stage t
    | TmPair (tm1, tm2, _) ->
      is_value_exn ~stage tm1;
      is_value_exn ~stage tm2
    | TmId tm -> is_value_exn ~stage tm
    (* Misc *)
    | IntImmidiate _ | BoolImmidiate _ -> ()
    | _ -> raise NotValue)
  (* when stage is not empty *)
  | v when not (Stage.is_empty stage) ->
    (match v with
    | TmVariable _ -> ()
    | TmLam (_, _, tm) -> is_value_exn ~stage tm
    | TmApp (tm1, tm2) ->
      is_value_exn ~stage tm1;
      is_value_exn ~stage tm2
    | Quote (a, t) -> is_value_exn ~stage:(Stage.add_classifier a stage) t
    | Escape (a, t) ->
      let a', rest = Stage.remove_classifier stage in
      assert (a = a');
      is_value_exn ~stage:rest t
    | Gen (_, t) -> is_value_exn ~stage t
    | GenApp (t, _) -> is_value_exn ~stage t
    | TmPair (tm1, tm2, _) ->
      is_value_exn ~stage tm1;
      is_value_exn ~stage tm2
    | TmFst tm -> is_value_exn ~stage tm
    | TmSnd tm -> is_value_exn ~stage tm
    | TmId tm -> is_value_exn ~stage tm
    | TmIdpeel (tm_eq, _, _) -> is_value_exn ~stage tm_eq
    | Csp (a, t) ->
      let a', rest = Stage.remove_classifier stage in
      assert (a = a');
      is_value_exn ~stage:rest t
    (* Misc *)
    | IntImmidiate _ | BoolImmidiate _ -> ()
    | TmIf (cond, do_if, do_else) ->
      is_value_exn ~stage cond;
      is_value_exn ~stage do_if;
      is_value_exn ~stage do_else
    | BinOp (_, tm1, tm2) ->
      is_value_exn ~stage tm1;
      is_value_exn ~stage tm2
    | TmLet (_, t1, t2) ->
      is_value_exn ~stage t1;
      is_value_exn ~stage t2
    | _ -> raise NotValue)
  | _ -> raise NotValue
;;

let is_value ~stage t =
  try
    is_value_exn ~stage t;
    true
  with
  | NotValue -> false
;;

let fun_of_op op i1 i2 =
  match op with
  | Plus -> IntImmidiate (i1 + i2)
  | Mult -> IntImmidiate (i1 * i2)
  | Div -> IntImmidiate (i1 / i2)
  | Lt -> BoolImmidiate (i1 < i2)
  | Lte -> BoolImmidiate (i1 <= i2)
  | Gt -> BoolImmidiate (i1 > i2)
  | Gte -> BoolImmidiate (i1 >= i2)
  | Eq -> BoolImmidiate (i1 = i2)
  | _ -> raise (EvalError "fun_of_op: invalid operation")
;;

let fun_of_lop op b1 b2 =
  match op with
  | And -> BoolImmidiate (b1 && b2)
  | Or -> BoolImmidiate (b1 || b2)
  | Eq -> BoolImmidiate (b1 = b2)
  | _ -> raise (EvalError "fun_of_lop: invalid operation")
;;

(** One step evaluation. Returns [None] if there is no reduction. *)
let rec one_step_eval_opt tm ~stage ~env =
  match tm with
  (* === Axioms === *)
  (* E-Beta *)
  | TmApp (TmLam (x, _, tm_body), tm_arg) when Stage.is_empty stage ->
    subst_term ~source:x ~target:tm_arg tm_body |> Option.some
  (* E-StageBeta *)
  | Escape (a, Quote (b, t))
    when b = a && Stage.is_single stage && Stage.tail stage = Some a -> Some t
  (* E-GenApp *)
  | GenApp (Gen (a, tm), stage_arg) when Stage.is_empty stage ->
    subst_classifier_term ~source:a ~target:stage_arg tm |> Option.some
  (* E-Fst *)
  | TmFst (TmPair (tm1, tm2, _))
    when is_value ~stage tm1 && is_value ~stage tm2 && Stage.is_empty stage ->
    tm1 |> Option.some
  (* E-Snd *)
  | TmFst (TmPair (tm1, tm2, _))
    when is_value ~stage tm1 && is_value ~stage tm2 && Stage.is_empty stage ->
    tm1 |> Option.some
  (* E-Idpeel *)
  | TmIdpeel (TmId y, x, t) when Stage.is_empty stage ->
    subst_term ~source:x ~target:y t |> Option.some
  (* E-Csp *)
  | Csp (_, t) ->
    let fv = freevars t in
    if fv = []
    then Some t
    else raise (EvalError ("CSP: free variables found for " ^ string_of_tm t))
  (* Misc *)
  | BinOp (op, IntImmidiate i1, IntImmidiate i2) when Stage.is_empty stage ->
    fun_of_op op i1 i2 |> Option.some
  | BinOp (op, BoolImmidiate b1, BoolImmidiate b2) when Stage.is_empty stage ->
    fun_of_lop op b1 b2 |> Option.some
  | TmIf (BoolImmidiate b, body_if, body_else) when Stage.is_empty stage ->
    (if b then body_if else body_else) |> Option.some
  | TmLet (x, v1, t2) when is_value ~stage v1 ->
    subst_term ~source:x ~target:v1 t2 |> Option.some
  (* === Congruence Rules === *)
  (* E-Abs *)
  | TmLam (x, ty_arg, t) when Stage.is_empty stage |> not ->
    one_step_eval_opt ~stage ~env t >>| fun t' -> TmLam (x, ty_arg, t')
  (* E-App2 *)
  | TmApp (v1, t2) when is_value ~stage v1 ->
    one_step_eval_opt ~stage ~env t2 >>| fun t2' -> TmApp (v1, t2')
  (* E-App1 *)
  | TmApp (t1, t2) -> one_step_eval_opt ~stage ~env t1 >>| fun t1' -> TmApp (t1', t2)
  (* E-SndInner *)
  | TmPair (v1, t2, ty) when is_value ~stage v1 ->
    one_step_eval_opt ~stage ~env t2 >>| fun t2' -> TmPair (v1, t2', ty)
  (* E-Quote *)
  | Quote (a, t) ->
    let stage' = stage |> Stage.add_classifier a in
    t |> one_step_eval_opt ~stage:stage' ~env >>| fun t' -> Quote (a, t')
  (* E-Escape *)
  | Escape (a, t) when Stage.tail stage = Some a ->
    let _, stage' = Stage.remove_classifier stage in
    t |> one_step_eval_opt ~stage:stage' ~env >>| fun t -> Escape (a, t)
  (* E-GenAppInner *)
  | GenApp (t, stage_b) ->
    one_step_eval_opt ~stage ~env t >>| fun t' -> GenApp (t', stage_b)
  (* E-Gen *)
  | Gen (a, t) -> one_step_eval_opt ~stage ~env t >>| fun t' -> Gen (a, t')
  (* E-Id *)
  | TmId t -> t |> one_step_eval_opt ~stage ~env >>| fun t' -> TmId t'
  (* E-IdpeelInnerR *)
  (* | TmIdpeel (v1, x, t) when is_value ~stage v1 -> *)
  (* t |> one_step_eval_opt ~stage ~env >>| fun t' -> TmIdpeel (v1, x, t') *)
  (* E-IdpeelInnerL *)
  | TmIdpeel (t1, x, t) ->
    t1 |> one_step_eval_opt ~stage ~env >>| fun t1' -> TmIdpeel (t1', x, t)
  (* Misc *)
  | BinOp (op, v1, t2) when is_value ~stage v1 ->
    t2 |> one_step_eval_opt ~stage ~env >>| fun t2' -> BinOp (op, v1, t2')
  | BinOp (op, t1, t2) ->
    t1 |> one_step_eval_opt ~stage ~env >>| fun t1' -> BinOp (op, t1', t2)
  | TmIf (tm_cond, tm_if, tm_else) ->
    tm_cond
    |> one_step_eval_opt ~stage ~env
    >>| fun tm_cond' -> TmIf (tm_cond', tm_if, tm_else)
  | TmLet (x, t1, t2) ->
    t1 |> one_step_eval_opt ~stage ~env >>| fun t1' -> TmLet (x, t1', t2)
  | TmVariable x -> E.lookup_exn x env |> Option.some
  | v when is_value ~stage v -> None
  | v ->
    let _ = v |> show_tm |> print_endline in
    let _ =
      "one_stage_eval_opt: progress violation for term: " ^ string_of_tm tm
      |> print_endline
    in
    raise (NotExpected "one_stage_eval_opt")
;;

(** Perform [one_step_eval_opt] until the term saturates. *)
let rec eval_term tm ~stage ~env =
  let loop tm =  (* AI: This function is better inline-expanded *)
    match one_step_eval_opt ~stage ~env tm with
    | Some tm' -> eval_term ~stage ~env tm'
    | None -> tm
  in
  loop tm
;;

(*
.............................................　..

　　　　　　　　　 ∧_,,,
　　　　　　　　　(ﾟ-;;ﾟ#)
　　　　　　　　　 |;; ;;∪
　　　　　　　　　 |;;; ;;;|～
;;:.. ..,,., ..,;;iﾙv,.. ..,.U"U...,;:. ..,;;:;"
　　　　. .;. . .　　,;;:.';'"" ''　　.,　　　　
*)
