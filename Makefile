builder = dune
target = main

default: main.exe

.PHONY: test clean

main.exe:
	dune build main.exe --profile release

test:
	dune runtest --profile release

doc:
	dune build @doc --profile release
	# mv ./_build/default/_doc/_html ./docs

parser:
	cd src; menhir --explain parser.mly

.PHONY: clean clean/parser
clean:
	dune clean

clean/parser:
	rm src/parser.ml src/parser.mli
