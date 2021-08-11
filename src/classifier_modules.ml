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
  val to_string : t -> string
  val to_index : t -> EqIndex.t

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

  exception EmptyStage
  exception OperationFailed
end = struct
  type t = classifier list [@@deriving show]

  exception EmptyStage
  exception OperationFailed

  let empty () = []
  let from_list l = l

  let to_string = function
    | [] -> "@_"
    | t ->
      t
      |> List.map ~f:(fun c -> "_" ^ string_of_classifier c)
      |> String.concat ~sep:""
      |> ( ^ ) "@"
  ;;

  let to_index stage =
    List.fold_right
      stage
      ~f:(fun accum classifier -> accum |> EqIndex.add_promote classifier)
      ~init:(EqIndex.empty ())
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
end

(** Implements equivalence index using [classifier]. *)
and EqIndex : sig
  (** Equivalence index and redution index *)
  type t [@@deriving show]

  val empty : unit -> t
  val to_string : t -> string
  val add_promote : t -> classifier -> t
  val add_demote : t -> classifier -> t
  val is_empty : t -> bool

  (** Concatenate stage and equivalence index. [concat_to_stage stage index] calculates [stage ++ index] *)
  val concat_to_stage : Stage.t -> t -> t

  (** Whether to allow beta reduction *)
  val allow_beta_reduction : t -> bool

  (** Whether to allow code manipulation *)
  val allow_code_manipulation : t -> bool

  (** Returns [true] when the index has no demote classifiers. *)
  val is_zero_or_positive : t -> bool
end = struct
  exception OperationFailed

  type index_classifier =
    | Promote of classifier
    | Demote of classifier
  [@@deriving show]

  type t = index_classifier list [@@deriving show]

  let empty () = []

  let string_of_index_classifier = function
    | Promote x -> "+" ^ string_of_classifier x
    | Demote x -> "-" ^ string_of_classifier x
  ;;

  let to_string t =
    let content = t |> List.map ~f:string_of_index_classifier |> String.concat ~sep:"" in
    "(" ^ content ^ ")"
  ;;

  let add_promote index classifier = Promote classifier :: index
  let add_demote index classifier = Demote classifier :: index
  let is_empty index = index = []

  (* TODO: check form of index *)
  let rec is_zero_or_positive = function
    | Promote _ :: rest -> is_zero_or_positive rest
    | Demote _ :: _rest -> false
    | [] -> true
  ;;

  let allow_beta_reduction index = is_zero_or_positive index
  let allow_code_manipulation index = is_empty index

  let rec concat_to_stage stage = function
    | [] -> stage |> Stage.to_index
    | Promote c :: rest_of_index ->
      concat_to_stage (stage |> Stage.add_classifier c) rest_of_index
    | Demote c :: rest_of_index ->
      (match Stage.remove_classifier stage with
      | c', rest_of_stage ->
        if c = c'
        then concat_to_stage rest_of_stage rest_of_index
        else raise OperationFailed)
  ;;
end
[@@deriving show]
