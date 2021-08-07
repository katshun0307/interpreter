open Tester
module S = Lfeqc__.Syntax
module E = Lfeqc__.Algorithmic_equivalence
module C = Lfeqc__.Tyenv.Tyenv

let () =
  let open S in
  { name = "alpha equivalent"
  ; func =
      (fun x ->
        try
          E.judge_alpha_equivalence x;
          true
        with
        | E.NotAlphaEquivalent _ -> false)
  ; prep = (fun x -> x)
  ; ishow = (fun (x, y) -> string_of_tm x ^ ", " ^ string_of_tm y)
  ; oshow = string_of_bool
  ; iprep = (fun (x, y) -> parse_term x, parse_term y)
  ; oprep = id
  ; cmp = ( = )
  ; dataset =
      [ { input = "3", "3"; expected = true }
      ; { input = "hoge", "hoge"; expected = false }
      ; { input = "hoge", "fuga"; expected = false }
      ; { input = "3", "1 + 2"; expected = false }
      ; { input = "3", "y"; expected = false }
      ; { input = "\\x: Int. 3 + x", "\\y:Int. 3 + y"; expected = true }
      ; { input = "\\x: Int. 3 + x", "\\y:Int. 3 + x"; expected = false }
      ; { input = "\\x: eq{int} (3+3) 6. x", "\\x: eq{int} (3+3) 6. x"; expected = true }
      ; { input = "\\x: eq{int} 6 6. x", "\\x: eq{int} (3+3) 6. x"; expected = true }
      ]
  }
  |> run_test_case
  |> ignore
;;

(* { name = "algorithmic term equivalence"
  ; func =
      (fun x ->
        try
          E.judge_term_equivalence (C.empty ()) 0 0 x;
          true
        with
        | E.NotAlphaEquivalent _ -> false)
  ; prep = (fun x -> x)
  ; ishow = (fun (x, y) -> string_of_tm x ^ ", " ^ string_of_tm y)
  ; oshow = string_of_bool
  ; iprep = (fun (x, y) -> parse_term x, parse_term y)
  ; oprep = id
  ; cmp = ( = )
  ; dataset =
      [ { input = "3", "3"; expected = true }
      ; { input = "x", "x"; expected = true }
      ; { input = "3", "y"; expected = false }
      ; { input = "lam x: Int. 3 + x", "lam y:Int. 3 + y"; expected = true }
      ; { input = "lam x: Int. 3 + x", "lam y:Int. 3 + x"; expected = false }
      ; { input =
            ( "{3, next(3 + 5):: sigma x:int. int code}"
            , "{3, next(3 + 5):: sigma x:int. int code}" )
        ; expected = true
        }
      ; { input =
            ( "{3, next(3 + 5):: sigma x:int. int code}"
            , "{3, next(3 + 8):: sigma x:int. int code}" )
        ; expected = false
        }
      ; { input = "lam x: eq{int} (3+3) 6. x", "lam x: eq{int} (3+3) 6. x"
        ; expected = true
        }
      ; { input = "lam x: eq{int} 6 6. x", "lam x: eq{int} (3+3) 6. x"; expected = true }
      ; { input = "lam x: eq{int} (3+3) 6. x", "lam x: eq{int} 7 7. x"; expected = false }
      ]
  }
  |> run_test_case
  |> ignore;
  { name = "algorithmic reduction"
  ; func = E.alogrithmic_reduction 0
  ; prep = (fun x -> x)
  ; ishow = string_of_tm
  ; oshow = string_of_tm
  ; iprep = parse_term
  ; oprep = parse_term
  ; cmp = ( = )
  ; dataset =
      [ { input = "3 + 3"; expected = "6" }
      ; { input = "id{3 + 3}"; expected = "id{6}" }
      ; { input = "lam x: eq{int} 3 ( 1 + 2). x"; expected = "lam x:eq{int} 3 3.x" }
      ; { input = "next(3 + prev(next 4))"; expected = "next(3 + 4)" }
      ; { input =
            "next(let hoge = prev(next(let hoge = let hoge = 4 in hoge * hoge in hoge * \
             hoge)) in hoge * hoge)"
        ; expected =
            "next(let hoge = let hoge = let hoge = 4 in hoge * hoge in hoge * hoge in \
             hoge * hoge)"
        }
      ]
  }
  |> run_test_case
  |> ignore *)
