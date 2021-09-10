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
    | None -> Some tm)
  (* === Axioms === *)
  (* EA-Beta *)
  | TmApp (TmLam (x, _, t1), t2) when EqIndex.allow_beta_reduction index ->
    Some (subst_term ~source:x ~target:t2 t1)
  (* EA-StageBeta *)
  | Escape (a, Quote (b, t)) when b = a && EqIndex.allow_code_manipulation index -> Some t
  (* EA-GenApp *)
  | GenApp (Gen (a, t), stage) ->
    subst_classifier_term ~source:a ~target:stage t |> Option.some
  (* EA-Fst *)
  | TmFst (TmPair (t1, _, _)) -> Some t1
  (* EA-Snd *)
  | TmSnd (TmPair (_, t2, _)) -> Some t2
  (* EA-Idpeel *)
  | TmIdpeel (TmId a, x, t) -> Some (subst_term ~source:x ~target:a t)
  (* EA-Csp *)
  | Csp (a, t) when EqIndex.has_demote_classifier_head a index -> Some t
  (* TODO: add this match case *)
  (* === Congruence rules that need special treatment === *)
  (* EA-Abs, EA-AbsTy *)
  | TmLam (x, ty, tm) ->
    let ty' = algorithmic_reduction_type ~index ~env ty in
    let tm' = algorithmic_reduction_term ~index ~env tm in
    Some (TmLam (x, ty', tm'))
  (* EA-Quote *)
  | Quote (a, t) ->
    let t' =
      t
      |> generic_map_term
           ~map:(algorithmic_reduction_axioms ~index:(index |> EqIndex.add_demote a) ~env)
    in
    Some (Quote (a, t'))
  (* EA-Escape *)
  | Escape (a, t) ->
    let t' =
      t
      |> generic_map_term
           ~map:
             (algorithmic_reduction_axioms ~index:(index |> EqIndex.add_promote a) ~env)
    in
    Some (Escape (a, t'))
  (* Additional constructs *)
  | BinOp (op, IntImmidiate i1, IntImmidiate i2) when EqIndex.allow_beta_reduction index
    -> fun_of_op op i1 i2 |> Option.some
  | BinOp (op, BoolImmidiate b1, BoolImmidiate b2) when EqIndex.allow_beta_reduction index
    -> fun_of_lop op b1 b2 |> Option.some
  | TmLetRec (f, TmLam (x, _, tm11), tm2) when EqIndex.allow_beta_reduction index ->
    let dummyenv = ref (E.empty ()) in
    let newenv = env |> E.extend f (ProcV (x, tm11, dummyenv)) in
    let _ = dummyenv := newenv in
    Some (tm2 |> generic_map_term ~map:(algorithmic_reduction_axioms ~index ~env:newenv))
  | _ -> None

(** Single step of algorithmic reduction on terms.
          This function is not strictly one step evaluation.
          It applies one step evaluation to multiple independent subterms. *)
and algorithmic_reduction_term ~index ~env =
  generic_map_term ~map:(algorithmic_reduction_axioms ~index ~env)

(** Sigle step of algorithmic reduction on types. *)
and algorithmic_reduction_type ~index ~env =
  generic_map_type ~maptm:(algorithmic_reduction_term ~index ~env) ~mapty:(fun _ -> None)
;;

(** Algorithmic normal form of term [tm] with [~index]. *)
let algorithmic_normal_form ~index ~env =
  let rec loop tm =
    let tm' = algorithmic_reduction_term tm ~index ~env in
    if tm' = tm then tm else loop tm'
  in
  loop
;;

(** Algorithmic normal form of type [ty] with [~index]. *)
let algorithmic_normal_form_type ~index ~env =
  let rec loop ty =
    let ty' = algorithmic_reduction_type ty ~index ~env in
    if ty' = ty then ty else loop ty'
  in
  loop
;;
