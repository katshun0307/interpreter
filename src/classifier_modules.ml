(** define syntax modules related to classifier *)
open Core

exception NotImplemented

let ( = ) = Stdlib.( = )

(** single classifier *)
type classifier = Classifier of string [@@deriving show]

let string_of_classifier = function
  | Classifier x -> x
;;

(** Implements stages using [classifier]. *)
module rec Stage : sig
  type t [@@deriving show]

  val empty : unit -> t
  val from_list : classifier list -> t
  val to_list : t -> classifier list
  val to_string : t -> string

  (** Add classifier to stage  *)
  val add_classifier : classifier -> t -> t

  (** Remove one classifier from stage. Returns empty stage when called to empty stage *)
  val remove_classifier : t -> classifier * t

  (** Remove classifier if it matches with given classifier, raise [OperationFailed] if not. *)
  val remove_classifier_exn : classifier -> t -> t

  (** Get the tail of stage as [option]. *)
  val tail : t -> classifier option

  val compare : t * t -> equal:(classifier * classifier -> bool) -> bool
  val occur_check : classifier -> t -> bool
  val fold_right : t -> f:(classifier -> 'a -> 'a) -> init:'a -> 'a
  val fold_left : t -> init:'b -> f:('b -> classifier -> 'b) -> 'b

  (* val fold_left : t -> f:(classifier -> 'a -> 'a) -> init:'a -> 'a *)
  val is_empty : t -> bool
  val is_single : t -> bool
  val is_above : low:t -> high:t -> bool
  val allow_beta_reduction : stage:t -> index:t -> bool
  val allow_code_manipulation : stage:t -> index:t -> classifier:classifier -> bool

  exception EmptyStage
  exception OperationFailed
end = struct
  type t = classifier list [@@deriving show]

  exception EmptyStage
  exception OperationFailed

  let empty () = []
  let from_list l = l
  let to_list l = l

  let to_string = function
    | [] -> "@_"
    | t ->
      t
      |> List.map ~f:(fun c -> "_" ^ string_of_classifier c)
      |> String.concat ~sep:""
      |> ( ^ ) "@"
  ;;

  let add_classifier = List.cons

  let remove_classifier = function
    | c :: rest -> c, rest
    | [] -> raise EmptyStage
  ;;

  let remove_classifier_exn a = function
    | classifier :: rest when classifier = a -> rest
    | _ as stage ->
      printf
        "cannot remove classifier %s from stage %s\n"
        (string_of_classifier a)
        (to_string stage);
      raise OperationFailed
  ;;

  let tail = Core.List.hd

  let compare stages_pair ~equal =
    let rec loop = function
      | cl1 :: rest1, cl2 :: rest2 -> equal (cl1, cl2) && loop (rest1, rest2)
      | [], [] -> true
      | _ -> false
    in
    loop stages_pair
  ;;

  let occur_check c = List.exists ~f:(fun c' -> c = c')
  let fold_right = List.fold_right
  let fold_left = List.fold_left

  (* let fold_left = List.fold_left *)
  let is_empty = ( = ) []
  let is_single t = List.length t = 1

  let rec is_above ~low ~high =
    match List.rev low, List.rev high with
    | [], _ -> true
    | a :: low', b :: high' when a = b -> is_above ~low:low' ~high:high'
    | _ -> false
  ;;

  let allow_beta_reduction ~stage ~index = is_above ~low:stage ~high:index

  let allow_code_manipulation ~stage ~index ~classifier =
    let classifier', stage' = remove_classifier stage in
    classifier = classifier' && is_above ~low:stage' ~high:index
  ;;
end
