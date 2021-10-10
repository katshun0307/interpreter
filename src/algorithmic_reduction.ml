open Syntax
open Classifier_modules
open Eval
module E = Environment.Environment

(** Algorithmic reduction on terms and types. *)

(** Axioms for algorithmic reduction. *)
let rec algorithmic_reduction_axioms tm ~(stage : Stage.t) ~(index : Stage.t) ~env =
  match tm with
  | TmVariable x when Stage.is_empty index || true (* TODO: check this condition *) ->
    (match E.lookup x env with
    | Some v -> Some v
    | None -> Some tm)
  (* === Axioms === *)
  (* EA-Beta *)
  | TmApp (TmLam (x, _, t1), t2) when Stage.allow_beta_reduction ~stage ~index ->
    Some (subst_term ~source:x ~target:t2 t1)
  (* EA-StageBeta *)
  | Escape (a, Quote (b, t))
    when b = a && Stage.allow_code_manipulation ~stage ~index ~classifier:a -> Some t
  (* EA-GenApp *)
  | GenApp (Gen (a, t), stage) when Stage.allow_beta_reduction ~stage ~index ->
    subst_classifier_term ~source:a ~target:stage t |> Option.some
  (* EA-Fst *)
  | TmFst (TmPair (t1, _, _)) when Stage.allow_beta_reduction ~stage ~index -> Some t1
  (* EA-Snd *)
  | TmSnd (TmPair (_, t2, _)) when Stage.allow_beta_reduction ~stage ~index -> Some t2
  (* EA-Idpeel *)
  | TmIdpeel (TmId a, x, t) when Stage.allow_beta_reduction ~stage ~index ->
    Some (subst_term ~source:x ~target:a t)
  (* EA-Csp *)
  | Csp (a, t) when Stage.allow_code_manipulation ~stage ~index ~classifier:a -> Some t
  (* === Congruence rules that need special treatment === *)
  (* EA-Abs, EA-AbsTy *)
  | TmLam (x, ty, tm) ->
    let ty' = algorithmic_reduction_type ~stage ~index ~env ty in
    let tm' = algorithmic_reduction_term ~stage ~index ~env tm in
    Some (TmLam (x, ty', tm'))
  (* EA-Quote *)
  | Quote (a, t) ->
    let t' =
      t
      |> generic_map_term
           ~map:
             (algorithmic_reduction_axioms
                ~stage:(stage |> Stage.add_classifier a)
                ~index
                ~env)
    in
    Some (Quote (a, t'))
  (* EA-Escape *)
  | Escape (a, t) ->
    let t' =
      t
      |> generic_map_term
           ~map:
             (algorithmic_reduction_axioms
                ~stage:(stage |> Stage.remove_classifier_exn a)
                ~index
                ~env)
    in
    Some (Escape (a, t'))
  (* Additional constructs *)
  | BinOp (op, IntImmidiate i1, IntImmidiate i2)
    when Stage.allow_beta_reduction ~stage ~index -> fun_of_op op i1 i2 |> Option.some
  | BinOp (op, BoolImmidiate b1, BoolImmidiate b2)
    when Stage.allow_beta_reduction ~stage ~index -> fun_of_lop op b1 b2 |> Option.some
  | TmLetRec (f, TmLam (x, _, tm11), tm2) when Stage.allow_beta_reduction ~stage ~index ->
    let dummyenv = ref (E.empty ()) in
    let newenv = env |> E.extend f (ProcV (x, tm11, dummyenv)) in
    let _ = dummyenv := newenv in
    Some
      (tm2
      |> generic_map_term ~map:(algorithmic_reduction_axioms ~stage ~index ~env:newenv))
  | _ -> None

(** Single step of algorithmic reduction on terms.
          This function is not strictly one step evaluation.
          It applies one step evaluation to multiple independent subterms. *)
and algorithmic_reduction_term ~(stage : Stage.t) ~(index : Stage.t) ~env =
  generic_map_term ~map:(algorithmic_reduction_axioms ~stage ~index ~env)

(** Single step of algorithmic reduction on types. *)
and algorithmic_reduction_type ~(stage : Stage.t) ~(index : Stage.t) ~env =
  generic_map_type ~maptm:(algorithmic_normal_form ~stage ~index ~env) ~mapty:(fun ty ->
      match ty with
      | TyQuote (a, ty') ->
        TyQuote
          ( a
          , algorithmic_reduction_type
              ~stage:(Stage.add_classifier a stage)
              ~index
              ~env
              ty' )
        |> Option.some
      | _ -> None)

(** Algorithmic normal form of term [tm] with [~index]. *)
and algorithmic_normal_form ~(stage : Stage.t) ~(index : Stage.t) ~env =
  let rec loop tm =
    let tm' = algorithmic_reduction_term tm ~stage ~index ~env in
    if tm' = tm then tm else loop tm'
  in
  loop
;;

(** Algorithmic normal form of type [ty] with [~index]. *)
let algorithmic_normal_form_type ~(stage : Stage.t) ~(index : Stage.t) ~env =
  let rec loop ty =
    let ty' = algorithmic_reduction_type ty ~stage ~index ~env in
    if ty' = ty then ty else loop ty'
  in
  loop
;;
