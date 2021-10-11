open OUnit
open Core
module S = Lfeqc__.Syntax
module Log = Lfeqc__.Syntax.Log
module Main = Lfeqc
module L = Lfeqc__.Lexer
module P = Lfeqc__.Parser
module T = Lfeqc__.Algorithmic_typing
module E = Lfeqc__.Eval
module Eq = Lfeqc__.Algorithmic_equivalence

exception TestError
exception NotImplemented

let ( = ) = Stdlib.( = )

type ('a, 'b) testcase =
  { input : 'a
  ; expected : 'b
  }

let gen_tests ?(cmp = ( = )) ~ishow ~oshow ~iprep ~oprep ~exec tests =
  tests
  |> List.map ~f:(fun (test : ('a, 'b) testcase) ->
         ""
         >:: fun () ->
         let actual = exec @@ iprep @@ test.input in
         assert_bool
           (Printf.sprintf
              "input:     '%s'\nactual:    %s\nexpected:  %s\n"
              (ishow @@ iprep @@ test.input)
              (oshow actual)
              (oshow @@ oprep @@ test.expected))
           (cmp actual (test.expected |> oprep)))
;;

let id x = x

let parse s =
  try P.toplevel L.main (Lexing.from_string (s ^ ";;")) with
  | _ ->
    Log.error "failed to parse_term: %s" s;
    raise TestError
;;

let parse_term s =
  s
  |> parse
  |> function
  | Term t -> t
  | _ ->
    Log.error "failed to parse_term: %s" s;
    raise TestError
;;

let parse_type s =
  try P.typing L.main (Lexing.from_string (s ^ ";;")) with
  | _ as e -> raise e
;;

let get_res s =
  (* run multiple command program statements *)
  let lexbuf = Lexing.from_string s in
  Main.silent_run lexbuf ()
;;

let run s =
  let open Main in
  match get_res s with
  | ProgRes { var; ty_opt; tm_opt } -> { var; ty_opt; tm_opt }
  | _ -> raise NotImplemented
;;

let check_run res expected =
  let open Main in
  match expected with
  | { var; ty_opt; tm_opt } ->
    let var_flag = var |> Option.value_map ~default:true ~f:(fun x -> res.var = Some x) in
    let ty_flag =
      ty_opt |> Option.value_map ~default:true ~f:(fun x -> res.ty_opt = Some x)
    in
    let tm_flag =
      tm_opt |> Option.value_map ~default:true ~f:(fun x -> res.tm_opt = Some x)
    in
    var_flag && ty_flag && tm_flag
;;

let raises_error s =
  match get_res s with
  | Main.RunError _ -> true
  | _ -> false
;;

type ('a, 'b, 'c, 'd, 'f) test =
  { name : string
  ; func : 'f
  ; prep : 'f -> 'a -> 'b
  ; ishow : 'a -> string
  ; oshow : 'b -> string
  ; iprep : 'c -> 'a
  ; oprep : 'd -> 'b
  ; cmp : 'b -> 'b -> bool
  ; dataset : ('c, 'd) testcase list
  }

let run_test_case (case : ('a, 'b, 'c, 'd, 'f) test) =
  Log.info "running test case: %s" case.name;
  run_test_tt_main
    (case.name
    >::: gen_tests
           ~cmp:case.cmp
           ~ishow:case.ishow
           ~oshow:case.oshow
           ~iprep:case.iprep
           ~oprep:case.oprep
           ~exec:(case.prep case.func)
           case.dataset)
;;
