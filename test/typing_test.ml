open Core
open Tester
module S = Mdeq__.Syntax
module Env = Mdeq__.Environment.Environment

let var_x = S.User "x"

let () =
  let open S in
  { name = "apply_subst"
  ; func = (fun ty -> U.apply_subst ([ 0, TyInt ], []) ty) (*; func= id*)
  ; prep = (fun x -> x)
  ; ishow = string_of_ty
  ; oshow = string_of_ty
  ; iprep = id
  ; oprep = id
  ; cmp = ( = )
  ; dataset =
      [ (* { input = TyPi (var_x, TyVar (0, []), Circ (TyVar (0, [])))
        ; expected = TyPi (var_x, TyInt, Circ TyInt)
        } *) ]
  }
  |> run_test_case
  |> ignore;
  { name = "unify"
  ; func = (fun tyconst -> U.unify (Env.empty ()) (tyconst, []))
  ; (* func= id; *)
    prep = (fun x -> x)
  ; ishow = U.string_of_type_constraints
  ; oshow = U.string_of_subst
  ; iprep = id
  ; oprep = (fun x -> x, [])
  ; cmp =
      (fun (l1, _) (l2, _) ->
        List.for_all l1 ~f:(fun x -> List.exists l2 ~f:(( = ) x))
        && List.for_all l2 ~f:(fun x -> List.exists l1 ~f:(( = ) x)))
  ; dataset =
      [ { input = [ TyVar (0, []), TyInt ]; expected = [ 0, TyInt ] }
      ; { input =
            (let ty_arg = TyVar (fresh_tyvar (), []) in
             let ty_res = TyVar (fresh_tyvar (), []) in
             [ ( TyPi (User "hoge", ty_arg, ty_res)
               , TyPi (var_x, TyInt, TyApp (TyFamily "Vector", TmVariable var_x)) )
             ])
        ; expected = [ 0, TyInt; 1, TyApp (TyFamily "Vector", TmVariable (User "hoge")) ]
        }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "unify_term"
  ; func = U.unify_term (Env.empty ()) (*; func= id*)
  ; prep = (fun x -> x)
  ; ishow = U.string_of_term_constraints
  ; oshow = (fun x -> U.string_of_subst ([], x))
  ; iprep = id
  ; oprep = id
  ; cmp = ( = )
  ; dataset =
      [ { input = [ IntImmidiate 3, IntImmidiate 3 ]; expected = [] }
      ; { input = [ TyTmVar 0, IntImmidiate 3 ]; expected = [ 0, IntImmidiate 3 ] }
        (* ; { input =
            [ ( Next (BinOp (Plus, IntImmidiate 3, IntImmidiate 4))
              , Next (BinOp (Plus, IntImmidiate 3, Prev (Next (IntImmidiate 4)))) )
            ]
        ; expected = []
        } *)
      ]
  }
  |> run_test_case
  |> ignore
;;
