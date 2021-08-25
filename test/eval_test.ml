open Core
open Tester
module Cl = Lfeqc__.Classifier_modules
module Env = Lfeqc__.Environment.Environment

let empty_stage = Cl.Stage.empty ()
let empty_env = Env.empty ()

let () =
  let open S in
  let open E in
  { name = "eval_term"
  ; func = eval_term ~stage:empty_stage ~env:empty_env
  ; prep = (fun x -> x)
  ; ishow = string_of_tm
  ; oshow = string_of_tm
  ; iprep = parse_term
  ; oprep = parse_term
  ; cmp = ( = )
  ; dataset =
      [ { input = "(<_a >_a 3)"; expected = "3" }
      ; { input = "(/\\_a. >_a 4) @_b"; expected = ">_b 4" }
      ]
  }
  |> run_test_case
  |> ignore
;;
