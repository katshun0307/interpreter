open Syntax
open Classifier_modules
open Eval
module E = Environment.Environment

(** Algorithmic reduction on terms and types. *)

exception NotNormalized

let rec normalize_tree t =
  match t with
  (* calc *)
  | BinOp (op, IntImmidiate i1, IntImmidiate i2) -> fun_of_op op i1 i2
  | BinOp (op, BoolImmidiate i1, BoolImmidiate i2) -> fun_of_lop op i1 i2
  (* each child is single *)
  | BinOp (Plus, IntImmidiate 0, t) | BinOp (Plus, t, IntImmidiate 0) ->
    t |> normalize_tree
  | BinOp (Mult, IntImmidiate 0, t) | BinOp (Mult, t, IntImmidiate 0) -> IntImmidiate 0
  | BinOp (Mult, IntImmidiate 1, t) | BinOp (Mult, t, IntImmidiate 1) ->
    t |> normalize_tree
  | BinOp (And, BoolImmidiate true, t) | BinOp (And, t, BoolImmidiate true) ->
    t |> normalize_tree
  | BinOp (And, BoolImmidiate false, t) | BinOp (And, t, BoolImmidiate false) ->
    BoolImmidiate false
  | BinOp (Or, BoolImmidiate false, t) | BinOp (Or, t, BoolImmidiate false) ->
    t |> normalize_tree
  | BinOp (Or, BoolImmidiate true, t) | BinOp (Or, t, BoolImmidiate true) ->
    BoolImmidiate true
  | BinOp (op, TmVariable tmv1, TmVariable tmv2) ->
    if Stdlib.( > ) tmv1 tmv2 then BinOp (op, TmVariable tmv2, TmVariable tmv1) else t
  (* immediate and single binop *)
  (* reorder *)
  | BinOp ((Plus as op), (IntImmidiate _ as tm2), (TmVariable _ as tm1))
  | BinOp ((Mult as op), (IntImmidiate _ as tm2), (TmVariable _ as tm1)) ->
    BinOp (op, tm1, tm2)
  | BinOp (Plus, IntImmidiate i1, BinOp (Plus, TmVariable tmv, IntImmidiate i2))
  | BinOp (Plus, BinOp (Plus, TmVariable tmv, IntImmidiate i2), IntImmidiate i1) ->
    BinOp (Plus, TmVariable tmv, fun_of_op Plus i1 i2)
  | BinOp (Mult, IntImmidiate i1, BinOp (Mult, TmVariable tmv, IntImmidiate i2))
  | BinOp (Mult, BinOp (Mult, TmVariable tmv, IntImmidiate i2), IntImmidiate i1) ->
    BinOp (Mult, TmVariable tmv, fun_of_op Mult i1 i2)
  (* Recur *)
  | BinOp (op, t1, t2) as t ->
    let t' = BinOp (op, t1 |> normalize_tree, t2 |> normalize_tree) in
    if t = t' then t else t' |> normalize_tree
  | _ as t -> t
;;

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
  | BinOp (_, _, _) as binop ->
    let binop' = binop |> normalize_tree in
    if binop' = binop then None else Some binop'
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
