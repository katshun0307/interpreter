open Core
open Syntax
open Classifier_modules

let ( = ) = Stdlib.( = )

(* x:(n) T *)
type tybinding = tm_var * Stage.t * ty [@@deriving show]

(* x:(n) K *)
type kindbinding = ty_family * Stage.t * kind [@@deriving show]

module Tyenv : sig
  type t

  val empty : unit -> t

  (** Add type-binding [(x, stage, ty)].  *)
  val extend_tybind : tybinding -> t -> t

  val ( *: ) : t -> tybinding -> t

  (** Add kind-binding [(x, stage, kind)].  *)
  val extend_kindbind : kindbinding -> t -> t

  val ( *:: ) : t -> kindbinding -> t
  val exists_tybind : tybinding -> t -> bool
  val exists_kindbind : kindbinding -> t -> bool
  val lookup_type : tm_var -> Stage.t -> t -> ty
  val lookup_csp_type : tm_var -> t -> Stage.t * ty
  val lookup_kind : ty_family -> Stage.t -> t -> kind
  val lookup_csp_kind : ty_family -> t -> Stage.t * kind

  (** Returns [true] when classifier occurs in any of type binding stages *)
  val classifier_occurcheck : classifier -> t -> bool

  val string_of_tyenv : t -> string
end = struct
  type t = tybinding list * kindbinding list

  let empty () = [], []
  let extend_tybind (data : tybinding) (tyenv, kindenv) = data :: tyenv, kindenv
  let extend_kindbind (data : kindbinding) (tyenv, kindenv) = tyenv, data :: kindenv
  let ( *: ) env bind = extend_tybind bind env
  let ( *:: ) env bind = extend_kindbind bind env

  let string_of_tyenv = function
    | tybind, kindbind ->
      let tybind_s =
        List.fold tybind ~init:"" ~f:(fun accum (ty_family, st, ty) ->
            accum
            ^ sprintf
                "%s:%s %s; "
                (string_of_tmvar ty_family)
                (st |> Stage.to_string)
                (string_of_ty ty))
      in
      let kindbind_s =
        List.fold kindbind ~init:"" ~f:(fun accum (ty_family, st, k) ->
            accum
            ^ sprintf "%s:%s %s; " ty_family (st |> Stage.to_string) (string_of_kind k))
      in
      "{" ^ tybind_s ^ "; " ^ kindbind_s ^ "}"
  ;;

  let exists_tybind (b : tybinding) ((tenv, _) : t) = List.exists ~f:(( = ) b) tenv
  let exists_kindbind b (_, kenv) = List.exists ~f:(( = ) b) kenv

  let lookup_type x stage ((tyenv, _) as con) =
    let r = List.find tyenv ~f:(fun (x', stage', _) -> x = x' && stage = stage') in
    match r with
    | Some (_, _, res) -> res
    | None ->
      raise
        (NoBindingException
           (sprintf
              "failed to lookup %s in stage %s on Tyenv {%s}"
              (string_of_tmvar x)
              (stage |> Stage.to_string)
              (string_of_tyenv con)))
  ;;

  let lookup_csp_type x ((tyenv, _) as con) =
    let r = List.find tyenv ~f:(fun (x', _, _) -> x = x') in
    match r with
    | Some (_, m, res) -> m, res
    | None ->
      raise
        (NoBindingException
           (sprintf
              "failed to lookup %s in tyenv {%s}"
              (string_of_tmvar x)
              (string_of_tyenv con)))
  ;;

  let lookup_kind x stage ((_, kindenv) as con) =
    let r = List.find kindenv ~f:(fun (x', stage', _) -> x = x' && stage = stage') in
    match r with
    | Some (_, _, res) -> res
    | None ->
      raise
        (NoBindingException
           (sprintf "failed to lookup %s in kindenv {%s}" x (string_of_tyenv con)))
  ;;

  let lookup_csp_kind x ((_, kindenv) as con) =
    let r = List.find kindenv ~f:(fun (x', _, _) -> x = x') in
    match r with
    | Some (_, m, res) -> m, res
    | None ->
      raise
        (NoBindingException
           (sprintf "failed to lookup %s in tyenv {%s}" x (string_of_tyenv con)))
  ;;

  let classifier_occurcheck (c : classifier) ((tybind, _) : t) =
    List.exists tybind ~f:(fun (_, stage, _) -> Stage.occur_check c stage)
  ;;
end
