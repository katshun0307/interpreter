{
let reservedWords = [
  (* Keywords *)
  (* ("else", Parser.ELSE); *)
  ("true", Parser.TRUE);
  ("false", Parser.FALSE);
  ("let", Parser.LET);
  ("in", Parser.IN);
  ("if", Parser.IF);
  ("then", Parser.THEN);
  ("else", Parser.ELSE);
  ("rec", Parser.REC);
  (* ("circ", Parser.CIRC); *)
  ("int", Parser.INT);
  ("bool", Parser.BOOL);
  ("sum", Parser.SIGMA);
  ("fst", Parser.FST);
  ("snd", Parser.SND);
  ("eq", Parser.EQ);
  ("id", Parser.EQID);
  ("idpeel", Parser.EQIDPEEL);
  ("prod", Parser.PI);
  ("run", Parser.RUN);
  (* ("code", Parser.CODE); *)
  ("type", Parser.TYPE);
  ("print_tyenv", Parser.PRCONT);
  ("change_stage", Parser.CHST);
]
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }

| "(*" { "(*" |> print_string; comment 1 lexbuf }

| "-"? ['0'-'9']+
    { Parser.INTV (int_of_string (Lexing.lexeme lexbuf)) }

| eof { Parser.EOF }
| "\\" { Parser.LAM }
| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| "{" { Parser.LCURLY }
| "}" { Parser.RCURLY }
| ";;" { Parser.SEMISEMI }
| "==" { Parser.EQUIV }
| "+" { Parser.PLUS }
| "*" { Parser.MULT }
| "/" { Parser.DIV }
| "~" { Parser.PROPER }
| "=" { Parser.EQUAL }
| "," { Parser.COMMA }
| "::" { Parser.DCOLON }
| ":" { Parser.COLON }
| "." { Parser.DOT }
| "#" { Parser.SHARP }
| "&&" { Parser.AND }
| "||" { Parser.OR }
| "<" { Parser.LT }
| ">" { Parser.GT }
| "<=" { Parser.LTE }
| ">=" { Parser.GTE }
| ">_" { Parser.QUOTE }
| "<_" { Parser.ESCAPE }
| "|>_" { Parser.QUOTETYPE }
| "/\\_" { Parser.GEN }
| "\\-/" { Parser.FORALL }
| "%" { Parser.CSP }
| "@" { Parser.ATMARK }
| "_" { Parser.UNDERBAR }

| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']*
    { let tyid = Lexing.lexeme lexbuf in
      Parser.TYID tyid
     }
| eof { exit 0 }

and comment i = parse
| "*)" { "*)" |> print_string; if i = 1 then ("\n" |> print_string; main lexbuf) else comment (i-1) lexbuf }
| "(*" { "(*" |> print_string; comment (i+1) lexbuf }
| _ { Lexing.lexeme lexbuf |> print_string; comment i lexbuf }
