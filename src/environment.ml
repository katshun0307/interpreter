open Core
open Syntax

let ( = ) = Stdlib.( = )

exception NotBound

module Environment : sig
  type 'a t = (tm_var * 'a) list

  val empty : unit -> 'a t
  val extend : tm_var -> 'a -> 'a t -> 'a t
  val lookup : tm_var -> 'a t -> 'a option
  val lookup_exn : tm_var -> 'a t -> 'a
  val map : ('a -> 'a) -> 'a t -> 'a t
  val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val to_string : f:('a -> string) -> 'a t -> string

  (* val reverse : t -> t *)
end = struct
  type 'a t = (tm_var * 'a) list

  let empty () = []
  let extend x v env = (x, v) :: env
  let lookup x env = List.Assoc.find ~equal:( = ) env x

  let lookup_exn x env =
    try List.Assoc.find_exn ~equal:( = ) env x with
    | Not_found_s _ -> raise NotBound
  ;;

  let rec map f = function
    | [] -> []
    | (id, v) :: rest -> (id, f v) :: map f rest
  ;;

  let rec fold_right f env a =
    match env with
    | [] -> a
    | (_, v) :: rest -> f v (fold_right f rest a)
  ;;

  let to_string ~f env =
    let s1 =
      env
      |> List.map ~f:(fun (tmv, x) -> sprintf "(%s, %s)" (string_of_tmvar tmv) (f x))
      |> String.concat ~sep:";"
    in
    "[" ^ s1 ^ "]"
  ;;
end
