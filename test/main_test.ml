open Core
open Tester
module S = Mdeq__.Syntax
module Main = Mdeq

let () =
  let open S in
  let open Main in
  { name = "TyDecl"
  ; func = run
  ; prep = id
  ; ishow = id
  ; oshow = string_of_progres
  ; iprep = id
  ; oprep = id
  ; cmp = check_run
  ; dataset =
      [ (* { input= "type hoge = int;;lam x: hoge. x;;"
           ; expected=
               {var= None; ty_opt= Some (TyPi ("x", TyInt, TyInt)); tm_opt= None}
           } *) ]
  }
  |> run_test_case
  |> ignore;
  { name = "Run"
  ; func = run
  ; prep = id
  ; ishow = id
  ; oshow = string_of_progres
  ; iprep = id
  ; oprep = id
  ; cmp = check_run
  ; dataset = []
  }
  |> run_test_case
  |> ignore;
  { name = "RunError"
  ; func = Tester.raises_error
  ; prep = id
  ; ishow = id
  ; oshow = string_of_bool
  ; iprep = id
  ; oprep = id
  ; cmp = ( = )
  ; dataset =
      [ (* {input= "let a = next(next(3 + 3));;run a;;"; expected= false} *)
        (* ; {input= "let a = 3 + 3;;run a;;"; expected= true}  *) ]
  }
  |> run_test_case
  |> ignore
;;
