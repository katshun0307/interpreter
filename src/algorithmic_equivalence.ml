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

exception NotAlphaEquivalentType of ty * ty

(** Checks if the two terms are alpha equivalent. Raises [NotAlphaEquivalent (tm1, tm2)] if not. *)
let rec judge_alpha_equivalence ?(var_pair = []) ?(classifier_pair = []) (tm1, tm2) =
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
    | TmLam (tvl, tyargl, tml), TmLam (tvr, tyargr, tmr) ->
      loop (tml, tmr) ~var_pair:((tvl, tvr) :: var_pair) ~classifier_pair;
      judge_alpha_equivalence_of_type ~var_pair ~classifier_pair (tyargl, tyargr)
    | TmApp (tml1, tml2), TmApp (tmr1, tmr2) ->
      loop_default (tml1, tmr1);
      loop_default (tml2, tmr2)
    | TmPair (tml1, tml2, tyl), TmPair (tmr1, tmr2, tyr) ->
      loop_default (tml1, tmr1);
      loop_default (tml2, tmr2);
      judge_alpha_equivalence_of_type ~var_pair ~classifier_pair (tyl, tyr)
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
    | tm1, tm2 -> raise (NotAlphaEquivalent (tm1, tm2))
  in
  loop ~var_pair ~classifier_pair (tm1, tm2)

(** Checks if the two types are alpha equivalent. Raises [NotAlphaEquivalentType (tm1, tm2)] if not. *)
and judge_alpha_equivalence_of_type ?(var_pair = []) ?(classifier_pair = []) (ty1, ty2) =
  let loop_default = judge_alpha_equivalence_of_type ~var_pair ~classifier_pair in
  match ty1, ty2 with
  | TyVar (x, _), TyVar (y, _) when x = y -> ()
  | TyFamily x, TyFamily y when x = y -> ()
  | TyInt, TyInt | TyBool, TyBool -> ()
  | TyPi (x, tyl1, tyl2), TyPi (y, tyr1, tyr2)
  | TySigma (x, tyl1, tyl2), TySigma (y, tyr1, tyr2) ->
    let _ = loop_default (tyl1, tyr1) in
    let _ =
      judge_alpha_equivalence_of_type
        ~var_pair:((x, y) :: var_pair)
        ~classifier_pair
        (tyl2, tyr2)
    in
    ()
  | TyApp (tyl, tml), TyApp (tyr, tmr) ->
    let _ = loop_default (tyl, tyr) in
    let _ = judge_alpha_equivalence ~var_pair ~classifier_pair (tml, tmr) in
    ()
  | Equality tyl, Equality tyr -> loop_default (tyl, tyr)
  | TyQuote (cl, tyl), TyQuote (cr, tyr)
    when classifier_pair |> List.exists ~f:(( = ) (cl, cr)) -> loop_default (tyl, tyr)
  | TyGen (cl, tyl), TyGen (cr, tyr) ->
    let _ =
      judge_alpha_equivalence_of_type
        ~var_pair
        ~classifier_pair:((cl, cr) :: classifier_pair)
        (tyl, tyr)
    in
    ()
  | _, _ -> raise (NotAlphaEquivalentType (ty1, ty2))
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

let is_equivalent_term ~tyenv ~stage ~index (tm1, tm2) =
  try
    let _ = judge_term_equivalence ~tyenv ~stage ~index (tm1, tm2) in
    true
  with
  | NotEquivalent -> false
;;

let is_equivalent_type ~tyenv ~stage ~index (ty1, ty2) =
  try
    let _ = judge_type_equivalence ~tyenv ~stage ~index (ty1, ty2) in
    true
  with
  | NotEquivalent -> false
;;

let is_equivalent_kind ~tyenv ~stage ~index (kind1, kind2) =
  try
    let _ = judge_kind_equivalence ~tyenv ~stage ~index (kind1, kind2) in
    true
  with
  | NotEquivalent -> false
;;
