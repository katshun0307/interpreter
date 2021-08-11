open Core
open Syntax
open Classifier_modules
open Algorithmic_equivalence
open Tyenv.Tyenv

let raise_not_expected tm =
  sprintf "judge_type: entered unexpected match case when typing %s" (string_of_tm tm)
  |> print_endline;
  raise (NotExpected "judge_type")
;;

(**
Typing, kinding and well-formed kind judgements in algorithmic system. *)

(** Judge type of the given [ty] under [stage] and [tyenv]. *)

let rec judge_type ~stage ~tyenv tm =
  match tm with
  (* TA-Var *)
  | TmVariable x ->
    let ty = lookup_type x stage tyenv in
    assert_kind ~stage ~tyenv ty Proper;
    ty
  (* TA-Abs *)
  | TmLam (x, ty_arg, t) ->
    TyPi (x, ty_arg, judge_type ~stage ~tyenv:(tyenv *: (x, stage, ty_arg)) t)
  (* TA-Pair *)
  | TmPair (t1, t2, (TySigma (x, ty_one, ty_two) as ty)) ->
    let ty_one' = judge_type ~stage ~tyenv t1 in
    let ty_two' = judge_type ~stage ~tyenv t2 in
    let _check_kinding = assert_kind ~stage ~tyenv ty Proper in
    let _check_equivalence =
      judge_type_equivalence ~tyenv ~stage ~index:(EqIndex.empty ()) (ty_one, ty_one')
    in
    let _check_equivalence =
      judge_type_equivalence
        ~tyenv
        ~stage
        ~index:(EqIndex.empty ())
        (ty_two', subst_type ~source:x ~target:t1 ty_two)
    in
    ty
  (* TA-App *)
  | TmApp (s, t) as tm ->
    let ty_fun = judge_type ~stage ~tyenv s in
    let ty_arg = judge_type ~stage ~tyenv t in
    (match ty_fun with
    | TyPi (x, ty_arg', ty_res') ->
      let _check_equivalence =
        judge_type_equivalence ~tyenv ~stage ~index:(EqIndex.empty ()) (ty_arg, ty_arg')
      in
      subst_type ~source:x ~target:t ty_res'
    | _ -> raise_not_expected tm)
    (* TA-Fst *)
  | TmFst t ->
    let ty_t = judge_type ~tyenv ~stage t in
    (match ty_t with
    | TySigma (_, ty_one, _) -> ty_one
    | _ -> raise NotImplemented)
    (* TA-Snd *)
  | TmSnd t ->
    let ty_t = judge_type ~tyenv ~stage t in
    (match ty_t with
    | TySigma (_, _, ty_two) -> ty_two
    | _ -> raise NotImplemented)
  (* TA-EqIntro *)
  | TmId t ->
    let ty_t = judge_type ~tyenv ~stage t in
    TyApp (TyApp (Equality ty_t, t), t)
  (* TA-EqElim *)
  | TmIdpeel (t_eq, x, t_body) as tm ->
    let eq_ty = judge_type ~tyenv ~stage t_eq in
    (match eq_ty with
    | TyApp (TyApp (Equality ty, s1), _) ->
      (* NOTE: uses [s1] (the first term of the equality type) to infer the type C x x id(x) *)
      let c_ty =
        judge_type ~tyenv:(tyenv *: (x, stage, ty)) ~stage t_body
        |> subst_type ~source:x ~target:s1
      in
      c_ty
    | _ -> raise_not_expected tm)
  (* TA-Quote *)
  | Quote (a, t) ->
    let ty_inner = judge_type ~tyenv ~stage:(Stage.add_classifier a stage) t in
    TyQuote (a, ty_inner)
  (* TA-Escape *)
  | Escape (a, t) as tm ->
    let ty_code = judge_type ~tyenv ~stage:(Stage.remove_classifier_exn a stage) t in
    (match ty_code with
    | TyQuote (b, ty_inner) when a = b -> ty_inner
    | _ -> raise_not_expected tm)
  (* TA-Gen *)
  | Gen (a, t) ->
    let inner_ty = judge_type ~tyenv ~stage t in
    TyGen (a, inner_ty)
  (* TA-GenApp *)
  | GenApp (t, st) as tm ->
    let ty = judge_type ~tyenv ~stage t in
    (match ty with
    | TyGen (a, inner_ty) -> subst_classifier_type ~source:a ~target:st inner_ty
    | _ -> raise_not_expected tm)
  (* TA-Csp *)
  | Csp (a, t) as tm ->
    let a', stage' = Stage.remove_classifier stage in
    if a = a' then judge_type ~stage:stage' ~tyenv t else raise_not_expected tm
  (* Misc *)
  | IntImmidiate _ -> TyInt
  | BoolImmidiate _ -> TyBool
  | (BinOp (Plus, t1, t2) | BinOp (Mult, t1, t2) | BinOp (Div, t1, t2))
    when assert_type ~stage ~tyenv t1 TyInt = ()
         && assert_type ~stage ~tyenv t2 TyInt = () -> TyInt
  | BinOp (Lt, t1, t2)
  | BinOp (Lte, t1, t2)
  | BinOp (Gt, t1, t2)
  | BinOp (Gte, t1, t2)
  | BinOp (Eq, t1, t2)
    when assert_type ~stage ~tyenv t1 TyInt = ()
         && assert_type ~stage ~tyenv t2 TyInt = () -> TyBool
  | (BinOp (And, t1, t2) | BinOp (Or, t1, t2) | BinOp (Eq, t1, t2))
    when assert_type ~stage ~tyenv t1 TyBool = ()
         && assert_type ~stage ~tyenv t2 TyBool = () -> TyBool
  | TmIf (t_cond, t_then, t_else) ->
    let _ = assert_type ~stage ~tyenv t_cond TyBool in
    let ty_then = judge_type ~tyenv ~stage t_then in
    let ty_else = judge_type ~tyenv ~stage t_else in
    let _ =
      judge_type_equivalence ~tyenv ~stage ~index:(EqIndex.empty ()) (ty_then, ty_else)
    in
    ty_then
  | TmLet (x, t1, t2) ->
    let ty1 = judge_type ~tyenv ~stage t1 in
    judge_type ~stage ~tyenv:(tyenv *: (x, stage, ty1)) t2
  | _ as t -> raise (NoBindingException ("judge_type: " ^ (t |> string_of_tm)))

(** Judge kind of the given [ty] under [stage] and [tyenv]. *)
and judge_kind ~stage ~tyenv = function
  (* KA-Var *)
  | TyFamily x ->
    let k = lookup_kind x stage tyenv in
    let _ = validate_kind ~stage ~tyenv k in
    k
  (* KA-Pi *)
  | TyPi (x, ty_arg, ty_res) ->
    let _ = assert_kind ~stage ~tyenv ty_arg Proper in
    let _ =
      assert_kind ~stage ~tyenv:(tyenv |> extend_tybind (x, stage, ty_arg)) ty_res Proper
    in
    Proper
  (* KA-App *)
  | TyApp (ty_fun, tm_arg) as ty ->
    (match judge_kind ~stage ~tyenv ty_fun with
    | KindPi (_, ty_arg', kind_ret) ->
      let ty_arg = judge_type ~stage ~tyenv tm_arg in
      let _ =
        judge_type_equivalence ~tyenv ~stage ~index:(EqIndex.empty ()) (ty_arg, ty_arg')
      in
      kind_ret
    | _ -> NotExpected (ty |> string_of_ty |> sprintf "failed to judge kind: %s") |> raise)
  (* KA-Sigma *)
  | TySigma (x, ty_arg, ty_res) ->
    let _ = assert_kind ~stage ~tyenv ty_arg Proper in
    let _ =
      assert_kind ~stage ~tyenv:(tyenv |> extend_tybind (x, stage, ty_arg)) ty_res Proper
    in
    Proper
  (* KA-Equiv *)
  | Equality ty ->
    let _ = assert_kind ~stage ~tyenv ty Proper in
    KindPi (System "x", ty, KindPi (System "x", ty, Proper))
  (* KA-Quote *)
  | TyQuote (a, ty) ->
    let _ = assert_kind ~stage:(stage |> Stage.add_classifier a) ~tyenv ty Proper in
    Proper
  (* KA-Gen *)
  | TyGen (a, ty) ->
    let kind = judge_kind ~stage ~tyenv ty in
    assert ((classifier_occurcheck a tyenv || Stage.occur_check a stage) = false);
    kind
  (* Misc *)
  | TyInt | TyBool -> Proper
  | TyVar _ -> raise NotImplemented

(** Check if [kind] is well-formed under [stage] and [tyenv]. *)
and validate_kind ~stage ~tyenv = function
  (* WFA-Star *)
  | Proper -> ()
  (* WfA-Pi *)
  | KindPi (tv, ty, kind) ->
    let _ = assert_kind ~stage ~tyenv ty Proper in
    let tyenv' = extend_tybind (tv, stage, ty) tyenv in
    let _ = validate_kind ~stage ~tyenv:tyenv' kind in
    ()
  | KindVar _ -> raise NotImplemented

(** Shorthand function to assert result of [judge_type]. *)
and assert_type ~stage ~tyenv tm ty = assert (judge_type ~stage ~tyenv tm = ty)

(** Shorthand function to assert result of [judge_kind]. *)
and assert_kind ~stage ~tyenv ty kind = assert (judge_kind ~stage ~tyenv ty = kind)
