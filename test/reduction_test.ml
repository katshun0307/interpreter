open Tester
open Mdeq__.Syntax
open Mdeq__.Algorithmic_reduction
open Mdeq__.Classifier_modules
module E = Mdeq__.Environment.Environment

let () =
  { name = "algorithmic normal form"
  ; func =
      algorithmic_normal_form
        ~stage:(Stage.empty ())
        ~index:(Stage.empty ())
        ~env:(E.empty ())
  ; prep = (fun x -> x)
  ; ishow = string_of_tm
  ; oshow = string_of_tm
  ; iprep = parse_term
  ; oprep = parse_term
  ; cmp = ( = )
  ; dataset =
      [ { input = "/\\_a. >_a (3 * 3)"; expected = "/\\_a. >_a (3 * 3)" }
      ; { input = "id{/\\_a. (>_a (3 * 3))}"; expected = "id{/\\_a. >_a (3 * 3)}" }
      ; { input = "id{(/\\_a. >_a (3 * 3)) @}"; expected = "id{9}" }
      ; { input = "(/\\_a. >_a (3 * 3)) @"; expected = "9" }
      ; { input = "(\\x:int. x + 3) 5"; expected = "8" }
      ; { input = "(\\x: int. /\\_a. >_a (3 * (%_a x))) 4"
        ; expected = "/\\_a. >_a (3 * 4)"
        }
      ; { input = "\\x:( eq{int} 3 (1 + 2)). 4"; expected = "\\x:(eq{int} 3 3). 4" }
      ; { input = "(\\z:int. z + 2) 4"; expected = "6" }
      ; { input = "\\z:int. ((\\y: int. y + 3) 3)"; expected = "\\z:int. 6" }
      ; { input = "\\x: (eq{int} 3 3). idpeel{x, (y) (\\z:int. z + 2) 4};;"
        ; expected = "\\x: (eq{int} 3 3). idpeel{x, (y) 6}"
        }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "algorithmic normal form type"
  ; func =
      algorithmic_reduction_type
        ~stage:(Stage.empty ())
        ~index:(Stage.empty ())
        ~env:(E.empty () |> E.extend (User "y") (parse_term ">_a (1 + 2)"))
  ; prep = (fun x -> x)
  ; ishow = string_of_ty
  ; oshow = string_of_ty
  ; iprep = parse_type
  ; oprep = parse_type
  ; cmp = ( = )
  ; dataset =
      [ { input = "int"; expected = "int" }
      ; { input = "prod x: int. bool"; expected = "prod x: int. bool" }
      ; { input = "prod x: int. eq{int} 3 (3 + 2)"; expected = "prod x:int. eq{int} 3 5" }
      ; { input = "prod x:int. eq{int} ((/\\_a. (>_a 3)) @) 3"
        ; expected = "prod x:int. eq{int} 3 3"
        }
      ; { input = "eq{int} 3 (1 + 2)"; expected = "eq{int} 3 3" }
      ; { input = "eq{|>_a int} y y"
        ; expected = "eq{|>_a int} (>_a (1 + 2)) (>_a (1 + 2))"
        }
      ; { input = "|>_a (eq{int} (<_a (>_a (1 + 2))) 3)"
        ; expected = "|>_a (eq{int} 3 3)"
        }
      ; { input = "|>_a (eq{int} (<_a y) 3)"; expected = "|>_a (eq{int} 3 3)" }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "normalize tree"
  ; func = normalize_tree
  ; prep = (fun x -> x)
  ; ishow = show_tm
  ; oshow = string_of_tm
  ; iprep = parse_term
  ; oprep = parse_term
  ; cmp = ( = )
  ; dataset =
      [ { input = "x"; expected = "x" }
      ; { input = "1 * x"; expected = "x * 1" }
      ; { input = "-1 * -1"; expected = "1" }
      ; { input = "1 * -1"; expected = "-1" }
      ; { input = "-1 * 1"; expected = "-1" }
      ; { input = "-1 * -1 * x"; expected = "x * 1" }
      ; { input = "-1 * -1"; expected = "1" }
      ; { input = "x * -1 * -1"; expected = "x * 1" }
        (* ; { input = "-1 * x * -1"; expected = "x" } *)
        (* ; { input = "-1 * -1 * -1 * x"; expected = "x * -1" } *)
        (* ; { input = "-1 * -1 * -1 * x"; expected = "y * -1" } *)
      ]
  }
  |> run_test_case
  |> ignore
;;
