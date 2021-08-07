open Core
open Syntax
open Tyenv
open Eval
open Classifier_modules
open Algorithmic_reduction
module E = Environment.Environment

exception NotEquivalent

(** Raised if the two terms are not alpha equivalent *)
exception NotAlphaEquivalent of tm * tm

(** Checks if the two terms are alpha equivalent. Raises [NotAlphaEquivalent (tm1, tm2)] if not. *)
let judge_alpha_equivalence =
  let rec loop (tm1, tm2) ~var_pair ~classifier_pair =
    let loop_default = loop ~var_pair ~classifier_pair in
    match tm1, tm2 with
    | TmVariable tvl, TmVariable tvr ->
      if List.exists var_pair ~f:(( = ) (tvl, tvr))
      then ()
      else raise (NotAlphaEquivalent (tm1, tm2))
    | (IntImmidiate _, IntImmidiate _ | BoolImmidiate _, BoolImmidiate _) when tm1 = tm2
      -> ()
    | BinOp (op1, tml1, tml2), BinOp (op2, tmr1, tmr2) when op1 = op2 ->
      loop_default (tml1, tmr1);
      loop_default (tml2, tmr2)
    | TmLam (tvl, _, tml), TmLam (tvr, _, tmr) ->
      loop (tml, tmr) ~var_pair:((tvl, tvr) :: var_pair) ~classifier_pair
    | TmApp (tml1, tml2), TmApp (tmr1, tmr2) ->
      loop_default (tml1, tmr1);
      loop_default (tml2, tmr2)
    | TmPair (tml1, tml2, _), TmPair (tmr1, tmr2, _) ->
      (* TODO: define equivalence for pairs rigidly *)
      loop_default (tml1, tmr1);
      loop_default (tml2, tmr2)
    | TmFst t1, TmFst t2 | TmSnd t1, TmSnd t2 -> loop_default (t1, t2)
    | (Quote (a, tm1), Quote (b, tm2) | Escape (a, tm1), Escape (b, tm2))
      when List.exists classifier_pair ~f:(( = ) (a, b)) -> loop_default (tm1, tm2)
    | Csp (a, tml), Csp (b, tmr) when List.exists classifier_pair ~f:(( = ) (a, b)) ->
      loop_default (tml, tmr)
    | Gen (a, tm1), Gen (b, tm2) ->
      loop (tm1, tm2) ~var_pair ~classifier_pair:((a, b) :: classifier_pair)
    | GenApp (tml1, stage_l), GenApp (tmr1, stage_r) ->
      if Stage.compare (stage_l, stage_r) ~equal:(fun pair ->
             List.exists ~f:(( = ) pair) classifier_pair)
      then loop_default (tml1, tmr1)
      else NotAlphaEquivalent (tm1, tm2) |> raise
    | TmId t1, TmId t2 -> loop_default (t1, t2)
    | TmIdpeel (t_eql, xl, dl), TmIdpeel (t_eqr, xr, dr) ->
      loop (dl, dr) ~var_pair:((xl, xr) :: var_pair) ~classifier_pair;
      loop_default (t_eql, t_eqr)
    | Run tm1, Run tm2 -> loop_default (tm1, tm2)
    | TmDummy x, TmDummy y -> assert (x = y)
    | TmLet (tvl, el1, el2), TmLet (tvr, er1, er2) ->
      loop_default (el1, er1);
      loop (el2, er2) ~var_pair:((tvl, tvr) :: var_pair) ~classifier_pair
    | ( TmIf (cond_l, consequence_l, alternative_l)
      , TmIf (cond_r, consequence_r, alternative_r) ) ->
      loop_default (cond_l, cond_r);
      loop_default (consequence_l, consequence_r);
      loop_default (alternative_l, alternative_r)
    (* TODO: TmLetRec *)
    | tm1, tm2 -> raise (NotAlphaEquivalent (tm1, tm2))
  in
  loop ~var_pair:[] ~classifier_pair:[]
;;

(** Judge term equivalence by using QA_ANF rule. *)
let rec judge_term_equivalence ~tyenv ~stage ~index (s, t) =
  ignore tyenv;
  ignore stage;
  (* QA-ANF *)
  let anf_s = algorithmic_normal_form ~index s in
  let anf_t = algorithmic_normal_form ~index t in
  judge_alpha_equivalence (anf_s, anf_t)

(** Judge type equivalence. *)
and judge_type_equivalence ~tyenv ~stage ~index (ty1, ty2) =
  match ty1, ty2 with
  (* QTA-Var *)
  | TyFamily x, TyFamily y when x = y -> ()
  (* QTA-Pi *)
  | TyPi (x1, ty_s1, ty_s2), TyPi (x2, ty_t1, ty_t2) ->
    assert (ty_s1 = ty_s2);
    judge_type_equivalence ~tyenv ~stage ~index (ty_s1, ty_t1);
    judge_type_equivalence
      ~tyenv:(Tyenv.extend_tybind (x1, stage, ty_s1) tyenv)
      ~stage
      ~index
      (ty_s2, subst_type ~source:x1 ~target:(TmVariable x2) ty_t2)
  (* QTA-Sigma *)
  | TySigma (_x, ty_s1, ty_t1), TySigma (_y, ty_s2, ty_t2) ->
    judge_type_equivalence ~tyenv ~stage ~index (ty_s1, ty_s2);
    judge_type_equivalence ~tyenv ~stage ~index (ty_t1, ty_t2)
  (* QTA-App *)
  | TyApp (ty1, tm1), TyApp (ty2, tm2) ->
    judge_type_equivalence ~tyenv ~stage ~index (ty1, ty2);
    judge_term_equivalence ~tyenv ~stage ~index (tm1, tm2)
  | ty1, ty2 when ty1 = ty2 -> ()
  | TyQuote _, _ | _, TyQuote _ -> raise NotImplemented
  | _ -> raise NotEquivalent

and judge_kind_equivalence ~tyenv ~stage ~index = function
  (* QKA-Star *)
  | Proper, Proper -> ()
  (* QKA-Pi *)
  | KindPi (x1, ty1, k1), KindPi (x2, ty2, k2) ->
    judge_type_equivalence ~tyenv ~stage ~index (ty1, ty2);
    judge_kind_equivalence
      ~tyenv:(Tyenv.extend_tybind (x1, stage, ty1) tyenv)
      ~stage
      ~index
      (k1, subst_kind ~source:x2 ~target:(TmVariable x1) k2)
  | _ -> raise NotEquivalent
;;
