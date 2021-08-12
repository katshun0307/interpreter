(** define syntax for language *)
open Core

open Classifier_modules

exception NoBindingException of string
exception OccurCheckError
exception NotExpected of string
exception NotBound
exception NotImplemented
exception EOF

let ( = ) = Stdlib.( = )

(** term variable *)
type tm_var =
  | User of string (* term variables defined by user *)
  | System of string (* term varibles defined by system *)
[@@deriving show]

(** type family, e.g. [Vector] *)
type ty_family = string [@@deriving show]

(** type variable for type inference *)
type tyvar = int [@@deriving show]

(** express unknown term in type with variable *)
type ty_tmvar = int [@@deriving show]

type kindvar = int [@@deriving show]

let fresh_int_generator () =
  let counter = ref 0 in
  let body () =
    let ret = !counter in
    counter := ret + 1;
    ret
  in
  body
;;

let fresh_tmvar =
  let generator = fresh_int_generator () in
  fun () ->
    let x = generator () in
    System (sprintf "tmvar_%i" x)
;;

let fresh_tyvar =
  let generator = fresh_int_generator () in
  fun () ->
    let x = generator () in
    x
;;

let fresh_ty_tmvar : unit -> ty_tmvar = fresh_int_generator ()
let fresh_kindvar : unit -> kindvar = fresh_int_generator ()

type op =
  | Plus
  | Mult
  | Div
  | Or
  | And
  | Lt
  | Lte
  | Gt
  | Gte
  | Eq
[@@deriving show]

type tm =
  | TmVariable of tm_var
  | IntImmidiate of int
  | BoolImmidiate of bool
  | BinOp of op * tm * tm
  | TmLam of tm_var * ty * tm
  | TmApp of tm * tm
  | TmPair of tm * tm * ty
  | TmFst of tm
  | TmSnd of tm
  | Quote of classifier * tm
  | Escape of classifier * tm
  | Csp of classifier * tm
  | Gen of classifier * tm (* /\_a.t *)
  | GenApp of tm * Stage.t
  | TmId of tm
  | TmIdpeel of tm * tm_var * tm
  | TmDummy of tm_var
  | TmLet of tm_var * tm * tm
  | TmLetRec of tm_var * tm * tm
  | TmIf of tm * tm * tm
  | Run of tm
  | TyTmVar of ty_tmvar
  | LamV of tm_var * ty * tm * (tm_var * tm) list
  | ProcV of tm_var * tm * (tm_var * tm) list ref

and ty =
  | TyVar of tyvar * pending_substs
      (** represents type substitutions that cannot be calculated because it is a type variable.
      [[x -> s][y -> t] ty] is represented [TyVar(ty, [(x, s);(y, t)])]*)
  | TyFamily of ty_family
  | TyInt
  | TyBool
  | TyPi of tm_var * ty * ty
  | TySigma of tm_var * ty * ty
  | TyApp of ty * tm
  | Equality of ty
  | TyQuote of classifier * ty
  | TyGen of classifier * ty

and pending_substs = (tm_var * tm) list [@@deriving show]

type annot_tm_var = tm_var * ty option [@@deriving show]

type kind =
  | Proper
  | KindPi of tm_var * ty * kind
  | KindVar of kindvar
[@@deriving show]

type repl_options =
  | PrintTyenv
  | ChangeStage of int
[@@deriving show]

(** User input to the REPL is decoded into this type *)
type program =
  | Term of tm
  | Help of repl_options
  | TMDecl of tm_var * tm
  | TMDeclAnnot of annot_tm_var * tm
  | TYDecl of string * ty
  | TmEquivalence of tm * tm
  | TyEquivalence of ty * ty
  | KindEquivalence of kind * kind
[@@deriving show]

(* === helper functions === *)

(** Generic map function on types. *)
let rec generic_map_type ty ~maptm ~mapty =
  match mapty ty with
  | Some x -> x
  | None ->
    let map_inner = generic_map_type ~maptm ~mapty in
    (match ty with
    | TyVar _ | TyFamily _ | TyInt | TyBool -> ty
    | TyPi (x, ty1, ty2) -> TyPi (x, map_inner ty1, map_inner ty2)
    | TySigma (x, ty1, ty2) -> TySigma (x, map_inner ty1, map_inner ty2)
    | TyApp (ty, tm) -> TyApp (map_inner ty, maptm tm)
    | Equality ty -> Equality (map_inner ty)
    | TyQuote (a, ty) -> TyQuote (a, map_inner ty)
    | TyGen (a, ty) -> TyGen (a, map_inner ty))
;;

(** Generic map function on terms. *)
let rec generic_map_term tm ~map =
  match map tm with
  | Some tm' -> tm'
  | None ->
    let map_inner = generic_map_term ~map in
    (match tm with
    | TmVariable _ | IntImmidiate _ | BoolImmidiate _ -> tm
    | BinOp (op, tm1, tm2) -> BinOp (op, map_inner tm1, map_inner tm2)
    | TmApp (tm1, tm2) -> TmApp (map_inner tm1, map_inner tm2)
    | TmPair (tm1, tm2, ty) -> TmPair (map_inner tm1, map_inner tm2, ty)
    | TmFst t -> TmFst (map_inner t)
    | TmSnd t -> TmSnd (map_inner t)
    | Quote (a, t) -> Quote (a, map_inner t)
    | Escape (a, t) -> Escape (a, map_inner t)
    | Csp (a, t) -> Csp (a, map_inner t)
    | Gen (a, t) -> Gen (a, map_inner t)
    | GenApp (tm, stage) -> GenApp (map_inner tm, stage)
    | TmIdpeel (tm1, tmv', tm2) -> TmIdpeel (map_inner tm1, tmv', map_inner tm2)
    | TmId tm1 -> TmId (map_inner tm1)
    | TmLam (tmv', ty, tm1) -> TmLam (tmv', ty, map_inner tm1)
    | TmDummy tv -> TmDummy tv
    | TmLet (tv, tm1, tm2) -> TmLet (tv, map_inner tm1, map_inner tm2)
    | TmLetRec (f, tm1, tm2) -> TmLetRec (f, map_inner tm1, map_inner tm2)
    | TmIf (tm_cond, tm1, tm2) -> TmIf (map_inner tm_cond, map_inner tm1, map_inner tm2)
    | Run tm -> Run (map_inner tm)
    | TyTmVar _ -> tm
    | LamV _ -> raise NotImplemented
    | ProcV _ -> raise (NotExpected "generic_map_term"))
;;

(* === Substitutions === *)

(** Map function for variable substitution on [tm] *)
let rec f_for_subst_term ~source ~target tm =
  let subst = generic_map_term ~map:(f_for_subst_term ~source ~target) in
  match tm with
  | TmVariable x -> if x = source then Some target else None
  | TmLam (tmv', ty, tm1) ->
    if tmv' = source
    then Some (TmLam (tmv', ty, tm1))
    else (
      let ty' = subst_type ~source ~target ty in
      Some (TmLam (tmv', ty', subst tm1)))
  | TmLet (tv, tm1, tm2) ->
    Some (TmLet (tv, subst tm1, if tv = source then tm2 else subst tm2))
  | TmLetRec (tv, tm1, tm2) ->
    Some (TmLetRec (tv, subst tm1, if tv = source then tm2 else subst tm2))
  | _ -> None

(** Map function for variable substituion on [ty]. *)
and f_for_subst_type ~source ~target ty =
  match ty with
  | TyVar (x, substs) -> Some (TyVar (x, (source, target) :: substs))
  | _ -> None

(** Substitute all free occurences of [source] with [target] in [tm] *)
and subst_term ~source ~target tm =
  generic_map_term ~map:(f_for_subst_term ~source ~target) tm

(** Substitute all free occurences of [source] with [target] in [ty] *)
and subst_type ~source ~target =
  generic_map_type
    ~maptm:(subst_term ~source ~target)
    ~mapty:(f_for_subst_type ~source ~target)
;;

let rec subst_kind ~source ~target = function
  | Proper -> Proper
  | KindPi (tmv', ty', kind') ->
    KindPi (tmv', subst_type ty' ~source ~target, subst_kind ~source ~target kind')
  | KindVar _ as kind -> kind
;;

(** Convert [[x -> abc] >_x t] to [>_a >_b >_c t] *)
let apply_stage_to_quote tm stage =
  Stage.fold_right ~init:tm ~f:(fun classifier accum -> Quote (classifier, accum)) stage
;;

(** Convert [[x -> abc] <_x t] to [<_c <_b <_a t] *)
let apply_stage_to_escape tm stage =
  Stage.fold_left ~init:tm ~f:(fun accum classifier -> Escape (classifier, accum)) stage
;;

(** Convert [[x -> abc] csp_x t] to [csp_c csp_b csp_a t] *)
let apply_stage_to_csp tm stage =
  Stage.fold_left ~init:tm ~f:(fun accum classifier -> Csp (classifier, accum)) stage
;;

let apply_stage_to_tyquote ty stage =
  Stage.fold_right ~init:ty ~f:(fun classifier accum -> TyQuote (classifier, accum)) stage
;;

(** Map function for classifier substitution *)
let rec f_for_subst_classifier ~source ~target tm =
  let subst = generic_map_term ~map:(f_for_subst_classifier ~source ~target) in
  match tm with
  | Quote (a, tm) ->
    if a = source
    then
      apply_stage_to_quote (tm |> subst_classifier_term ~source ~target) target
      |> Option.some
    else None
  | Escape (a, tm) ->
    if a = source
    then
      apply_stage_to_escape (tm |> subst_classifier_term ~source ~target) target
      |> Option.some
    else None
  | Csp (a, tm) ->
    if a = source
    then
      apply_stage_to_csp (tm |> subst_classifier_term ~source ~target) target
      |> Option.some
    else None
  | Gen (a, tm) -> if a = source then Some (Gen (a, tm)) else Some (Gen (a, subst tm))
  | _ -> None

and f_for_subst_classifier_type ~source ~target ty =
  match ty with
  | TyQuote (a, ty) when a = source -> apply_stage_to_tyquote ty target |> Option.some
  | TyGen (a, ty) when a = source -> TyGen (a, ty) |> Option.some
  | _ -> None

(** Substitute all free occurences of classifier [source] with stage [target] in [tm]. *)
and subst_classifier_term ~source ~target tm =
  generic_map_term ~map:(f_for_subst_classifier ~source ~target) tm

(** Substitute all free occurences of classifier [source] with stage [target] in [ty]. *)
and subst_classifier_type ~source ~target =
  generic_map_type
    ~maptm:(subst_classifier_term ~source ~target)
    ~mapty:(f_for_subst_classifier_type ~source ~target)
;;

(** Check if type variable [tv] does not occur in type.
  raise [OccurCheckError] if it occurs. *)
let rec tyvar_occurcheck tv = function
  | TyVar (x, _) when x = tv -> raise OccurCheckError
  | TyVar (_, _) | TyInt | TyBool | TyFamily _ -> ()
  | TyApp (ty, _) | Equality ty -> tyvar_occurcheck tv ty
  | TyPi (_, ty1, ty2) | TySigma (_, ty1, ty2) ->
    tyvar_occurcheck tv ty1;
    tyvar_occurcheck tv ty2
  | TyQuote (_, ty) -> tyvar_occurcheck tv ty
  | TyGen (_, ty) -> tyvar_occurcheck tv ty
;;

(** Check if type variable [tv] does not occur in kind.
  raise [OccurCheckError] if it occurs. *)
let rec kindvar_occurcheck kv = function
  | KindPi (_, _, k) -> kindvar_occurcheck kv k
  | Proper -> ()
  | KindVar x when x = kv -> raise OccurCheckError
  | KindVar _ -> ()
;;

(** @deprecated type for judgements *)
type judgement =
  (* | ValidTyenv of Tyenv.t *)
  | ValidKind of kind
  | TypeJudgement of tm * ty
  | KindJudgement of ty * kind

let string_of_tmvar = function
  | User x -> x
  | System x -> x
;;

let string_of_tyvar tv = "@@" ^ string_of_int tv

let string_of_op = function
  | Plus -> "+"
  | Mult -> "*"
  | Div -> "/"
  | And -> "&&"
  | Or -> "||"
  | Lt -> "<"
  | Lte -> "<="
  | Gt -> ">"
  | Gte -> ">="
  | Eq -> "="
;;

let rec string_of_kind = function
  | Proper -> "*"
  | KindPi (x, ty, k) ->
    sprintf "Π%s:%s. %s" (string_of_tmvar x) (string_of_ty ty) (string_of_kind k)
  | KindVar x -> sprintf "k@%i" x

and string_of_tm = function
  | TmVariable (User x) | TmVariable (System x) -> (x : string)
  | IntImmidiate i -> string_of_int i
  | BoolImmidiate b -> string_of_bool b
  | BinOp (Mult, (BinOp (Plus, _, _) as t1), (BinOp (Plus, _, _) as t2)) ->
    sprintf "(%s) %s (%s)" (string_of_tm t1) (string_of_op Mult) (string_of_tm t2)
  | BinOp (Mult, (BinOp (Plus, _, _) as t1), t2) ->
    sprintf "(%s) %s %s" (string_of_tm t1) (string_of_op Mult) (string_of_tm t2)
  | BinOp (Mult, t1, (BinOp (Plus, _, _) as t2)) ->
    sprintf "%s %s (%s)" (string_of_tm t1) (string_of_op Mult) (string_of_tm t2)
  | BinOp (op, t1, t2) ->
    sprintf "%s %s %s" (string_of_tm t1) (string_of_op op) (string_of_tm t2)
  | TmLam (x, arg_ty, tm) ->
    sprintf "\\%s: %s. %s" (string_of_tmvar x) (string_of_ty arg_ty) (string_of_tm tm)
  | TmApp (t1, t2) -> sprintf "%s %s" (string_of_tm t1) (string_of_tm t2)
  | TmPair (t1, t2, ty) ->
    sprintf "(%s, %s: %s)" (string_of_tm t1) (string_of_tm t2) (string_of_ty ty)
  | TmFst t -> sprintf "%s.fst" (string_of_tm t)
  | TmSnd t -> sprintf "%s.snd" (string_of_tm t)
  | Quote (a, t) -> sprintf "▶_%s %s" (a |> string_of_classifier) (t |> string_of_tm)
  | Escape (a, t) -> sprintf "◀_%s %s" (a |> string_of_classifier) (t |> string_of_tm)
  | Csp (a, t) -> sprintf "%%_%s %s" (a |> string_of_classifier) (t |> string_of_tm)
  | Gen (a, t) -> sprintf "Λ%s. %s" (a |> string_of_classifier) (t |> string_of_tm)
  | GenApp (tm, stage) ->
    sprintf "/\\_%s %s" (tm |> string_of_tm) (stage |> Stage.to_string)
  | TmId t -> sprintf "id(%s)" (string_of_tm t)
  | TmIdpeel (t1, tv, t2) ->
    sprintf "idpeel(%s, (%s)%s)" (string_of_tm t1) (string_of_tmvar tv) (string_of_tm t2)
  | TmDummy x -> sprintf "<Dummy_%s>" (string_of_tmvar x)
  | TmLet (x, tm1, tm2) ->
    sprintf "let %s = %s in %s" (string_of_tmvar x) (string_of_tm tm1) (string_of_tm tm2)
  | TmLetRec (f, tm1, tm2) ->
    sprintf
      "let rec %s = %s in %s"
      (string_of_tmvar f)
      (string_of_tm tm1)
      (string_of_tm tm2)
  | TmIf (tm1, tm2, tm3) ->
    sprintf
      "if %s then %s else %s"
      (string_of_tm tm1)
      (string_of_tm tm2)
      (string_of_tm tm3)
  | Run t -> sprintf "run %s" (string_of_tm t)
  | TyTmVar x -> sprintf "@@(%i)" x
  | LamV _ -> sprintf "<fun>"
  | ProcV (tmv, tm, _) ->
    sprintf "ProcV(%s, %s, env)" (string_of_tmvar tmv) (string_of_tm tm)

and string_of_ty = function
  | TyVar (tv, sub) ->
    "@"
    ^ (sub
      |> List.map ~f:(fun (x, y) ->
             sprintf "[%s |-> %s]" (string_of_tmvar x) (string_of_tm y))
      |> String.concat ~sep:"")
    ^ (tv |> string_of_tyvar)
  | TyFamily x -> x
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyPi (x, arg_ty, res_ty) ->
    sprintf
      "Pi %s: %s. %s"
      (string_of_tmvar x)
      (string_of_ty arg_ty)
      (string_of_ty res_ty)
  | TySigma (x, arg_ty, res_ty) ->
    sprintf
      "Sigma %s: %s. %s"
      (string_of_tmvar x)
      (string_of_ty arg_ty)
      (string_of_ty res_ty)
  | TyApp (ty, tm) -> sprintf "%s %s" (string_of_ty ty) (string_of_tm tm)
  | Equality ty -> sprintf "Eq_{%s}" (string_of_ty ty)
  | TyQuote (a, ty) -> sprintf "▷_%s %s" (a |> string_of_classifier) (ty |> string_of_ty)
  | TyGen (a, ty) -> sprintf "∀ %s.%s" (a |> string_of_classifier) (ty |> string_of_ty)
;;
