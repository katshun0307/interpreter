open Core
open Syntax
open Classifier_modules
open Tyenv
module E = Environment.Environment
open Eval

let load_file = ref ""

(* variables to values *)
type env =
  { mutable tm_env : tm E.t
  ; mutable ty_env : ty E.t
  }

(* Declarations for mutable values *)
let env = { tm_env = E.empty (); ty_env = E.empty () }
let tyenv = ref (Tyenv.empty ())
let stage = ref (Stage.empty ())
let debug = ref false
let srcfile = ref "-"

type progres =
  { var : tm_var option
  ; ty_opt : ty option
  ; tm_opt : tm option
  }

let print_debug_info s = if !debug then "DEBUG: " ^ s |> print_endline else ()

let string_of_progres { var; ty_opt; tm_opt } : string =
  sprintf
    "var: %s\tty_opt: %s\ttm_opt: %s\n"
    (var |> Option.map ~f:string_of_tmvar |> Option.value ~default:"None")
    (ty_opt |> Option.map ~f:string_of_ty |> Option.value ~default:"None")
    (tm_opt |> Option.map ~f:string_of_tm |> Option.value ~default:"None")
;;

type res =
  | ProgRes of progres
  | Meta of repl_options
  | Dummy
  | RunError of exn

type exec_result =
  { ty : ty
  ; tm : tm
  }

(** Return type and reduced value of term. *)
let exec_core (tm : tm) ~(ty_annot : ty option) : exec_result =
  let ty = Algorithmic_typing.judge_type ~tyenv:!tyenv ~stage:!stage ~env:env.tm_env tm in
  (* NOTE: apply algorithmic reduction on terms in dependent type *)
  let ty =
    Algorithmic_reduction.algorithmic_normal_form_type
      ~index:(EqIndex.empty ())
      ~env:env.tm_env
      ty
  in
  let _ = if !debug then ty |> string_of_ty |> print_endline else () in
  (* let _ =
    match ty_annot with
    | Some ty' -> ([ ty, ty' ], []) @^ constraint_of_subst subst |> unify env.tm_env
    | None -> ()
  in *)
  let _ = ty_annot in
  let v = Eval.eval_term ~env:env.tm_env ~stage:(Stage.empty ()) tm in
  let _ = if !debug then v |> string_of_tm |> print_endline else () in
  { ty; tm = v }
;;

let exec_meta = function
  | ChangeStage st -> stage := st
  | PrintTyenv -> !tyenv |> Tyenv.string_of_tyenv |> print_endline
  | HasType (tm, ty) ->
    let open Algorithmic_typing in
    let flag = has_type ~tyenv:!tyenv ~stage:!stage ~env:env.tm_env tm ty in
    flag |> string_of_bool |> print_endline
  | HasKind (ty, kind) ->
    let open Algorithmic_typing in
    let flag = has_kind ~tyenv:!tyenv ~stage:!stage ~env:env.tm_env ty kind in
    flag |> string_of_bool |> print_endline
;;

(* let flag = has_type *)

(** Execute parsed program *)
let exec p =
  if !debug then print_string (show_program p ^ "\n") else ();
  match p with
  | Term tm ->
    let result_core = exec_core tm ~ty_annot:None in
    ProgRes
      { var = Some (System "-")
      ; ty_opt = Some result_core.ty
      ; tm_opt = Some result_core.tm
      }
  | TMDecl (x, tm) ->
    let result_core = exec_core tm ~ty_annot:None in
    let tyenv' = Tyenv.extend_tybind (x, !stage, result_core.ty) !tyenv in
    let _ = tyenv := tyenv' in
    let tm_env' = E.extend x result_core.tm env.tm_env in
    env.tm_env <- tm_env';
    ProgRes { var = Some x; ty_opt = Some result_core.ty; tm_opt = Some result_core.tm }
  | TMDeclAnnot ((x, ty_annot), tm) ->
    let result_core = exec_core tm ~ty_annot in
    let tyenv' = Tyenv.extend_tybind (x, !stage, result_core.ty) !tyenv in
    tyenv := tyenv';
    let tm_env' = E.extend x result_core.tm env.tm_env in
    env.tm_env <- tm_env';
    (* let tm_env' = E.extend x (eval_term env.tm_env !stage tm) env.tm_env in *)
    (* let _ = ([ ty, ty' ], []) @^ constraint_of_subst subst |> unify env.tm_env in *)
    raise NotImplemented
  | TYDecl (x, ty) ->
    (* TODO: implement *)
    let ty_env' = E.extend (User x) ty env.ty_env in
    env.ty_env <- ty_env';
    ProgRes { var = Some (User "x"); ty_opt = Some ty; tm_opt = None }
  | Help option ->
    let _ = exec_meta option in
    Dummy
  | _ -> raise NotImplemented
;;

let show_result = function
  | ProgRes data ->
    printf
      "%s : %s = %s\n"
      (data.var |> Option.map ~f:string_of_tmvar |> Option.value ~default:"-")
      (data.ty_opt |> Option.map ~f:string_of_ty |> Option.value ~default:"-")
      (data.tm_opt |> Option.map ~f:string_of_tm |> Option.value ~default:"-")
  | Meta _ -> raise NotImplemented
  | Dummy -> ()
  | RunError e -> printf "RunError of %s" (e |> sexp_of_exn |> string_of_sexp)
;;

(** command line repl  *)
let rec repl () =
  print_string (sprintf "|-(%s) " (!stage |> Stage.to_string));
  Out_channel.flush stdout;
  if not !debug
  then (
    try
      let p = Parser.toplevel Lexer.main (Lexing.from_channel In_channel.stdin) in
      exec p |> show_result
    with
    | e -> e |> Exn.to_string |> print_endline)
  else (
    let p = Parser.toplevel Lexer.main (Lexing.from_channel In_channel.stdin) in
    exec p |> show_result);
  repl ()
;;

let execution_count = ref 0

(** file repl  *)
let rec file_repl lexbuf () =
  try
    let prog = Parser.toplevel Lexer.main lexbuf in
    (try
       printf "=== exec %d ===\n" !execution_count;
       execution_count := !execution_count + 1;
       exec prog |> show_result;
       Out_channel.flush stdout
     with
    | e ->
      (* error executing program *)
      (if not !debug
      then
        sprintf
          "=== ERROR ===\n%s\n%s------------"
          (show_program prog)
          (e |> Exn.to_string)
      else sprintf "=== ERROR ===\n%s\n------------" (e |> Exn.to_string))
      |> print_endline);
    file_repl lexbuf ()
  with
  | EOF ->
    (* end of program *)
    ()
  | e ->
    (* error parsing program *)
    e |> Exn.to_string |> print_endline
;;

let silent_run lexbuf () =
  (* for testing purposes, produces last result of program *)
  let rec loop lexbuf prev_res =
    try
      let prog = Parser.toplevel Lexer.main lexbuf in
      try
        let res = exec prog in
        loop lexbuf res
      with
      | e ->
        (* error in execution *)
        sprintf "=== ERROR ===\n%s\n------------" (show_program prog) |> print_endline;
        raise e
    with
    | EOF ->
      (* end of program, return result *)
      prev_res
    | e ->
      (* unexpected error parsing program *)
      RunError e
  in
  loop lexbuf Dummy
;;

let usage = "Usage: " ^ (Sys.get_argv ()).(0) ^ " [-test] [-load <filename>] [-debug]"

let aspec =
  Arg.align
    [ "-load", Arg.Set_string load_file, "load program before starting REPL"
    ; "-debug", Arg.Unit (fun () -> debug := true), "debug (output parse tree)"
    ]
;;

(** the main default REPL function *)
let main () =
  let _ = "=== LFEq◯  REPL ===\n" |> print_string in
  Arg.parse aspec (fun s -> srcfile := s) usage;
  if not (!load_file = "")
  then (
    (* execute file contents *)
    let inchan = In_channel.create !load_file in
    let lexbuf = Lexing.from_channel inchan in
    file_repl lexbuf ();
    repl ())
  else repl ()
;;
