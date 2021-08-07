open Syntax
open Classifier_modules
open Eval
module E = Environment.Environment

(** Algorithmic reduction on terms and types. *)

(** Axioms for algorithmic reduction. *)
let rec algorithmic_reduction_axioms tm ~index ~env =
  match tm with
  | TmVariable x when EqIndex.is_empty index ->
    (match E.lookup x env with
    | Some v -> Some v
    | None ->
      raise
        (EvalError
           (Printf.sprintf
              "variable %s not found in %s"
              (string_of_tmvar x)
              (E.to_string ~f:string_of_tm env))))
  | TmLam (x, ty, tm) ->
    let ty' = algoritmic_reduction_type ~index ~env ty in
    Some (TmLam (x, ty', tm))
    (* Binary operations *)
  | BinOp (op, IntImmidiate i1, IntImmidiate i2) when EqIndex.allow_beta_reduction index
    -> fun_of_op op i1 i2 |> Option.some
  | BinOp (op, BoolImmidiate b1, BoolImmidiate b2) when EqIndex.allow_beta_reduction index
    -> fun_of_lop op b1 b2 |> Option.some
  (* apply function to value *)
  | TmApp (LamV (x, _, tm_body, closure_env), tm_t)
    when EqIndex.allow_beta_reduction index ->
    let env' = E.extend x tm_t closure_env in
    let tm' = algoritmic_reduction_term ~env:env' ~index tm_body in
    tm' |> Option.some
  | TmApp (ProcV (x, tm1, env'), tm2) ->
    let tm' = subst_term ~source:x ~target:tm2 tm1 in
    algoritmic_reduction_term ~env:!env' ~index tm' |> Option.some
    (* | TmApp (TmLam (x, _, t1), t2) when EqIndex.is_empty index -> *)
    (* Some (subst_term ~source:x ~target:t2 t1) *)
    (* Pair operations *)
  | TmFst (TmPair (t1, _, _)) -> Some t1
  | TmSnd (TmPair (_, t2, _)) -> Some t2
  (* Stage operations *)
  | Quote (a, Escape (b, t)) when a = b && EqIndex.allow_code_manipulation index -> Some t
  | Escape (a, Quote (b, t)) when b = a && EqIndex.allow_code_manipulation index -> Some t
  | Quote (a, t) ->
    let t' =
      t
      |> generic_map_term
           ~map:(algorithmic_reduction_axioms ~index:(EqIndex.add_demote index a) ~env)
    in
    Some (Quote (a, t'))
  | Escape (a, t) ->
    let t' =
      t
      |> generic_map_term
           ~map:(algorithmic_reduction_axioms ~index:(EqIndex.add_promote index a) ~env)
    in
    Some (Escape (a, t'))
  | GenApp (Gen (a, t), stage) ->
    subst_classifier_term ~source:a ~target:stage t |> Option.some
  | TmIdpeel (a, x, t) -> Some (subst_term ~source:x ~target:a t)
  (* Additional constructs *)
  | TmLetRec (f, TmLam (x, _, tm11), tm2) when EqIndex.allow_beta_reduction index ->
    let dummyenv = ref (E.empty ()) in
    let newenv = env |> E.extend f (ProcV (x, tm11, dummyenv)) in
    let _ = dummyenv := newenv in
    Some (tm2 |> generic_map_term ~map:(algorithmic_reduction_axioms ~index ~env:newenv))
  | _ -> None

(** Single step of algorithmic reduction on terms.
    This function is not strictly one step evaluation.
    It applies one step evaluation to multiple independent subterms. *)
and algoritmic_reduction_term ~index ~env =
  generic_map_term ~map:(algorithmic_reduction_axioms ~index ~env)

(** Sigle step of algorithmic reduction on types. *)
and algoritmic_reduction_type ~index ~env =
  generic_map_type ~maptm:(algoritmic_reduction_term ~index ~env) ~mapty:(fun _ -> None)
;;

(** Algorithmic normal form of term [tm] with [~index]. *)
let algorithmic_normal_form ~index =
  let rec loop tm =
    let tm' = algoritmic_reduction_term tm ~index ~env:(E.empty ()) in
    if tm' = tm then tm else loop tm'
  in
  loop
;;

(** Algorithmic normal form of type [ty] with [~index]. *)
let algorithmic_normal_form_type ~index =
  let rec loop ty =
    let ty' = algoritmic_reduction_type ty ~index ~env:(E.empty ()) in
    if ty' = ty then ty else loop ty'
  in
  loop
;;
