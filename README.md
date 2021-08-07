
# lfeqc Interpreter

```
$ make
$ ledit ./lfeqc.exe
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
	| (t1, t2, T)
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
	| _				( empty stage )
	| _a			( single classifier )
	| _a<stage>		( list of classifiers )
```

## Examples

+ `let a = 3 in a + 4;;`
+ `(/\_x. >_x 4) @_;;`
+ `(/\_x. >_x 4) @_a_b;;`
+ `>_a (\x:int. >_a %_a x);;`
+ `(lam x: int. x + 4) 42;;`
+ `id{3}`
+ `idpeel{3, (x) x + 3}`
+ `idpeel{id{3}, (x) \m: (eq{int} x 3). m}`
+ `idpeel{id{3}, (x) \m: (eq{int} x 3). m} id{1+2}`
