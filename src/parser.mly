%{
open Syntax
open Classifier_modules
%}

// basics
%token LPAREN RPAREN SEMISEMI
%token LAM COLON DOT PI DCOLON
%token LCURLY RCURLY COMMA SIGMA
%token SHARP PRCONT CHST EOF UNDERBAR
// terms
%token LET IN IF THEN ELSE REC
%token EQ EQID EQIDPEEL EQUIV
%token RUN QUOTE ESCAPE GEN CSP ATMARK
%token FST SND
%token TRUE FALSE
// EQUIV PROPER
// operators
%token EQUAL PLUS MULT DIV
%token LT LTE GT GTE
%token OR AND
// types
%token INT BOOL
%token TYPE
%token FORALL QUOTETYPE
	// %token CODE CIRC
// kinds
%token PROPER

%token <int> INTV
%token <string> ID
%token <Syntax.ty_family> TYID

%start toplevel
%start <Syntax.program> toplevel

%start <Syntax.ty> typing
%%

toplevel :
  | e=TMExpr SEMISEMI { Term e }
  | LET x=UserID EQUAL tm=TMExpr SEMISEMI { TMDecl(x, tm) }
  | LET x=AnnotID EQUAL tm=TMExpr SEMISEMI { TMDeclAnnot(x, tm) }
  | TYPE x=ID EQUAL ty=TYExpr SEMISEMI { TYDecl(x, ty) }
//   | e=EquivExpr { e }
  | SHARP e=CommandExpr { Help e }
  | EOF { raise EOF }

// misc
UserID :
  | x=ID { User x }

AnnotID:
  | x=UserID COLON ty=TYExpr { (x, Some ty) }
  | LPAREN e=AnnotID RPAREN { e }

StageExpr:
  | ATMARK s=Stage { Stage.from_list s }

Stage:
  | UNDERBAR { [] }
  | UNDERBAR a=ID { [Classifier a] }
  | UNDERBAR a=ID rest=Stage { Classifier(a) :: rest }

ClassifierExpr:
  | a=ID { Classifier(a) }

// DeclExpr :
//   | LET x=UserID EQUAL tm=TMExpr { TMDecl(x, tm) }
//   | LET x=AnnotID EQUAL tm=TMExpr { TMDeclAnnot(x, tm) }
//   | TYPE x=ID EQUAL ty=TYExpr { TYDecl(x, ty) }

// EquivExpr :
//   | e1=TMExpr EQUIV e2=TMExpr SEMISEMI { TmEquivalence(e1, e2) }
//   | e1=TYExpr EQUIV e2=TYExpr SEMISEMI { TyEquivalence(e1, e2) }
//   | e1=KindExpr EQUIV e2=KindExpr SEMISEMI { KindEquivalence(e1, e2) }

CommandExpr :
  | PRCONT { PrintTyenv }
  | CHST i=INTV { ChangeStage i }


typing:
  | e=TYExpr SEMISEMI { e }

// types
TYExpr :
  | PI x=UserID COLON ty1=TYExpr DOT ty2=TYExpr { TyPi(x, ty1, ty2) }
  | SIGMA x=UserID COLON ty1=TYExpr DOT ty2=TYExpr { TySigma(x, ty1, ty2) }
  | e = TYAPPExpr { e }

TYAPPExpr :
  | ty1=TYAPPExpr tm2=AExpr { TyApp(ty1, tm2) }
  | ty=TYAExpr { ty }

TYAExpr :
  | x=TYID { TyFamily x }
  | QUOTETYPE a=ClassifierExpr ty=TYExpr { TyQuote(a, ty) }
  | FORALL a=ClassifierExpr ty=TYExpr { TyGen(a, ty) }
  | INT { TyInt }
  | BOOL { TyBool }
  | EQ LCURLY ty=TYExpr RCURLY { Equality ty }
  | LPAREN e=TYExpr RPAREN { e }

// terms
TMExpr :
  | e=EqExpr { e }
  | LET x=UserID EQUAL tm1=TMExpr IN tm2=TMExpr { TmLet(x, tm1, tm2) }
  | LET REC f=UserID EQUAL tm1=TMExpr IN tm2=TMExpr { TmLetRec(f, tm1, tm2) }
  | LAM x=UserID COLON arg_ty=TYExpr DOT tm=TMExpr { TmLam(x, arg_ty, tm) }
  | GEN a=ClassifierExpr DOT tm=TMExpr { Gen(a, tm) }
  | EQIDPEEL LCURLY tm1=TMExpr COMMA LPAREN x=UserID RPAREN tm2=TMExpr RCURLY { TmIdpeel(tm1, x, tm2) }
  | IF tm1=TMExpr THEN tm2=TMExpr ELSE tm3=TMExpr { TmIf(tm1, tm2, tm3) }

// KindExpr :
//   | PROPER { Proper }
//   | PI x=UserID COLON ty=TYExpr DOT e=KindExpr { KindPi(x, ty, e) }

EqExpr:
  | e1=OrExpr EQUAL e2=OrExpr { BinOp(Eq, e1, e2) }
  | e=OrExpr { e }

OrExpr:
  | e1=AndExpr OR e2=AndExpr { BinOp(Or, e1, e2) }
  | e=AndExpr { e }

AndExpr:
  | e1=AndExpr AND e2=LtExpr { BinOp(And, e1, e2) }
  | e=LtExpr { e }

LtExpr:
  | e1=PlusExpr op=LtOp e2=PlusExpr { BinOp(op, e1, e2) }
  | e=PlusExpr { e }

LtOp:
  | LT { Lt }
  | GT { Gt }
  | LTE { Lte }
  | GTE { Gte }

PlusExpr:
  | e1=PlusExpr PLUS e2=MultExpr { BinOp(Plus, e1, e2) }
  | e=MultExpr { e }

MultExpr:
  | e1=MultExpr MULT e2=AppExpr { BinOp(Mult, e1, e2) }
  | e1=MultExpr DIV e2=AppExpr { BinOp(Div, e1, e2) }
  | e=AppExpr { e }

AppExpr:
  | e1=AppExpr e2=AExpr { TmApp(e1, e2) }
  | e1=AppExpr a=StageExpr { GenApp(e1, a) }
  | e=AExpr { e }

AExpr :
  | QUOTE a=ClassifierExpr tm=AExpr { Quote(a, tm) }
  | ESCAPE a=ClassifierExpr tm=AExpr { Escape(a, tm) }
  | CSP UNDERBAR a=ClassifierExpr tm=AExpr { Csp(a, tm) }
  | i=UserID { TmVariable i }
  | i=INTV { IntImmidiate i }
  | TRUE   { BoolImmidiate true }
  | FALSE  { BoolImmidiate false }
  | e=AExpr DOT FST { TmFst e }
  | e=AExpr DOT SND { TmSnd e }
  | RUN e=AExpr { Run(e) } (* deprecated *)
  | EQID LCURLY tm=TMExpr RCURLY { TmId(tm) }
  | LCURLY t1=TMExpr COMMA t2=TMExpr DCOLON SIGMA x=UserID COLON s=TYExpr DOT t=TYExpr RCURLY { TmPair(t1, t2, TySigma(x, s, t)) }
  | LPAREN e=TMExpr RPAREN { e }
