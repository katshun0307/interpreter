open Tester
module S = Lfeqc__.Syntax
module C = Lfeqc__.Classifier_modules
open Lfeqc__.Classifier_modules

let var_x = S.User "x"

let () =
  let open S in
  { name = "subst_term"
  ; func = subst_term ~source:var_x ~target:(TmVariable (User "test_var"))
  ; prep = (fun x -> x)
  ; ishow = string_of_tm
  ; oshow = string_of_tm
  ; iprep = id
  ; oprep = id
  ; cmp = ( = )
  ; dataset =
      [ { input = TmVariable var_x; expected = TmVariable (User "test_var") }
      ; { input = TmLam (var_x, TyInt, BinOp (Plus, TmVariable var_x, IntImmidiate 3))
        ; expected = TmLam (var_x, TyInt, BinOp (Plus, TmVariable var_x, IntImmidiate 3))
        }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "subst_type"
  ; func = subst_type ~source:var_x ~target:(TmVariable (User "test_var"))
  ; prep = (fun x -> x)
  ; ishow = string_of_ty
  ; oshow = string_of_ty
  ; iprep = id
  ; oprep = id
  ; cmp = ( = )
  ; dataset =
      [ { input = TyFamily "x"; expected = TyFamily "x" }
      ; { input = TyInt; expected = TyInt }
      ; { input = TyApp (Equality TyInt, TmVariable var_x)
        ; expected = TyApp (Equality TyInt, TmVariable (User "test_var"))
        }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "apply_stage_to_csp"
  ; func = apply_stage_to_csp (IntImmidiate 3)
  ; prep = (fun x -> x)
  ; ishow = Stage.to_string
  ; oshow = show_tm
  ; iprep = (fun l -> l |> List.map (fun x -> Classifier x) |> Stage.from_list)
  ; oprep = parse_term
  ; cmp = ( = )
  ; dataset =
      [ { input = [ "x" ]; expected = "%_x 3" }
      ; { input = [ "x"; "y" ]; expected = "%_y %_x 3" }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "subst_classifier"
  ; func =
      subst_classifier_term
        ~source:(Classifier "x")
        ~target:([ Classifier "y" ] |> C.Stage.from_list)
  ; prep = (fun x -> x)
  ; ishow = string_of_tm
  ; oshow = string_of_tm
  ; iprep = parse_term
  ; oprep = parse_term
  ; cmp = ( = )
  ; dataset =
      [ { input = ">_x 3"; expected = ">_y 3" }
      ; { input = ">_x <_y >_x 3"; expected = ">_y <_y >_y 3" }
      ; { input = "/\\_x. >_x 3"; expected = "/\\_x. >_x 3" }
      ; { input = "/\\_ z. >_z >_x 3"; expected = "/\\_ z. >_z >_y 3" }
      ; { input = "%_a 3"; expected = "%_a 3" }
      ; { input = "%_x 3"; expected = "%_y 3" }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "subst_classifier_mult"
  ; func =
      subst_classifier_term
        ~source:(Classifier "x")
        ~target:([ Classifier "y"; Classifier "z" ] |> C.Stage.from_list)
  ; prep = (fun x -> x)
  ; ishow = string_of_tm
  ; oshow = string_of_tm
  ; iprep = parse_term
  ; oprep = parse_term
  ; cmp = ( = )
  ; dataset =
      [ { input = ">_x 3"; expected = ">_y >_z 3" }
      ; { input = ">_x <_y >_x 3"; expected = ">_y >_z <_y >_y >_z 3" }
      ; { input = "%_x 3"; expected = "%_z %_y 3" }
      ; { input = "/\\_x. >_x 3"; expected = "/\\_x. >_x 3" }
      ; { input = "/\\_a. >_a >_x 3"; expected = "/\\_a. >_a >_y >_z 3" }
      ; { input = "/\\_a. >_a <_x 3"; expected = "/\\_a. >_a <_z <_y 3" }
      ; { input = "/\\_x. %_x 3"; expected = "/\\_x. %_x 3" }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "subst_classifier_type"
  ; func =
      subst_classifier_type
        ~source:(Classifier "x")
        ~target:([ Classifier "y"; Classifier "z" ] |> C.Stage.from_list)
  ; prep = (fun x -> x)
  ; ishow = string_of_ty
  ; oshow = string_of_ty
  ; iprep = parse_type
  ; oprep = parse_type
  ; cmp = ( = )
  ; dataset =
      [ { input = "X"; expected = "X" }
      ; { input = "int"; expected = "int" }
      ; { input = "eq{int} >_a 3 >_a 3"; expected = "eq{int} >_a 3 >_a 3" }
      ; { input = "\\-/ x |>_x int"; expected = "\\-/ x |>_x int" }
      ; { input = "\\-/ zz |>_x int"; expected = "\\-/ zz |>_y |>_z int" }
      ; { input = "|>_x |>_zz int"; expected = "|>_y |>_z |>_zz int" }
      ; { input = "|>_x |>_zz int"; expected = "|>_y |>_z |>_zz int" }
      ]
  }
  |> run_test_case
  |> ignore
;;
