
# lfeqc Interpreter

```
$ make
$ ledit ./lfeqc.exe
$ ledit ./lfeqc.exe -load programs/hogefuga.lfeqc
```

```
Usage: ./lfeqc.exe [-test] [-load <filename>] [-debug]
  -load load   program before starting REPL
  -debug debug (output parse tree)
  -help        Display this list of options
```

## Syntax

```
t ::= [terms]
	| x 		['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
	| n
	| true | false
	| t op t
	| \x:T.t
	| t1 t2
	| {t1, t2 :: T}
	| t.fst
	| t.snd
	| id{t}
	| idpeel{t, (x) t}
	| t A
	| /\_a. t
	| >_a t
	| <_a t
	| %_a t
	| if t1 then t2 else t3
	| # [meta_options]
```

```
T ::= [types]
	| X			['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']*
	| int
	| bool
	| eq{T}
	| T t
	| sum x:T1.T2
	| prod x:T1.T2
	| \-/ a T
	| |>_a T
```

```
A ::= [Stages]
	| @stage

stage ::= [list of classifiers]
	| 				( empty stage )
	| stage_a		( list of classifiers )
```

```
meta_options ::=
	| print_tyenv
	| t has type T
	| T has kind K

## Examples

+ `let a = 3 in a + 4;;`
+ `(/\_x. >_x 4) @;;`
+ `(/\_x. >_x 4) @_a_b;;`
+ `>_a (\x:int. >_a %_a x);;`
+ `(\x: int. x + 4) 42;;`
+ `id{3};;`
+ `idpeel{3, (x) x + 3};;`
+ `idpeel{id{3}, (x) \m: (eq{int} x 3). m};;`
+ `idpeel{id{3}, (x) \m: (eq{int} x 3). m} id{1+2};;`
+ `# id{4 < 56} has type eq{bool} true true;;`