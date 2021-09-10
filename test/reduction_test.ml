open Tester
open Lfeqc__.Syntax
open Lfeqc__.Algorithmic_reduction
open Lfeqc__.Classifier_modules
module E = Lfeqc__.Environment.Environment

let () =
  { name = "algorithmic normal form"
  ; func = algorithmic_normal_form ~index:(EqIndex.empty ()) ~env:(E.empty ())
  ; prep = (fun x -> x)
  ; ishow = string_of_tm
  ; oshow = string_of_tm
  ; iprep = parse_term
  ; oprep = parse_term
  ; cmp = ( = )
  ; dataset =
      [ { input = "/\\_a. >_a (3 * 3)"; expected = "/\\_a. >_a (3 * 3)" }
      ; { input = "id{/\\_a. >_a (3 * 3)}"; expected = "id{/\\_a. >_a (3 * 3)}" }
      ; { input = "id{(/\\_a. >_a (3 * 3)) @_}"; expected = "id{9}" }
      ; { input = "(/\\_a. >_a (3 * 3)) @_"; expected = "9" }
      ; { input = "(\\x:int. x + 3) 5"; expected = "8" }
      ; { input = "(\\x: int. /\\_a. >_a (3 * %_a x)) 4"
        ; expected = "/\\_a. >_a (3 * %_a 4)"
        }
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
  ; func = algorithmic_reduction_type ~index:(EqIndex.empty ()) ~env:(E.empty ())
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
      ; { input = "prod x:int. eq{int} ((/\\_a. (>_a 3)) @_) 3"
        ; expected = "prod x:int. eq{int} 3 3"
        }
      ]
  }
  |> run_test_case
  |> ignore
;;
